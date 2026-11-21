#include "postgres.h"

#include <ctype.h>

#include "access/htup_details.h"
#include "catalog/pg_attribute.h"
#include "catalog/pg_enum.h"
#include "catalog/pg_type.h"
#include "fmgr.h"
#include "funcapi.h"
#include "lib/stringinfo.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "nodes/parsenodes.h"
#include "nodes/primnodes.h"
#include "parser/analyze.h"
#include "parser/parser.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteHandler.h"
#include "utils/builtins.h"
#include "utils/catcache.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/tuplestore.h"

PG_MODULE_MAGIC;

typedef enum ShapeKind
{
	SHAPE_SCALAR,
	SHAPE_OBJECT,
	SHAPE_ARRAY,
	SHAPE_UNKNOWN_JSON
} ShapeKind;

typedef struct Shape
{
	ShapeKind	kind;
	Oid			type;
	bool		nullable;
	bool		guessed;
	bool		json;
	bool		null_only;
	Oid			cast_from;
	List	   *fields;
	struct Shape *element;
} Shape;

typedef struct Field
{
	char	   *name;
	Shape	   *shape;
} Field;

typedef struct Scope
{
	Query	   *query;
	struct Scope *parent;
	Bitmapset  *present;
	List	   *nonnull;
} Scope;

typedef struct Row
{
	char	   *path;
	char	   *pg_type;
	bool		nullable;
	char	   *schema;
	char	   *note;
} Row;

static Shape *shape_expr(Scope *scope, Node *node);

static Shape *
make_shape(ShapeKind kind, Oid type, bool nullable)
{
	Shape	   *shape = palloc0(sizeof(Shape));

	shape->kind = kind;
	shape->type = type;
	shape->nullable = nullable;
	return shape;
}

static Shape *
copy_shape(Shape *shape)
{
	Shape	   *copy = palloc(sizeof(Shape));

	memcpy(copy, shape, sizeof(Shape));
	return copy;
}

static Shape *typed_shape(Oid type, bool nullable);
static Shape *typed_shape_dims(Oid type, bool nullable, int dims);
static Shape *relation_row(Oid relid, Oid rowtype);

static Shape *
guessed_shape(Oid type)
{
	Shape	   *shape = typed_shape(type, true);

	shape->guessed = true;
	return shape;
}

static bool
is_json_type(Oid type)
{
	return type == JSONOID || type == JSONBOID;
}

static bool
is_composite_type(Oid base)
{
	return OidIsValid(base) && base != RECORDOID && get_typtype(base) == TYPTYPE_COMPOSITE;
}

static Shape *
typed_shape_dims(Oid type, bool nullable, int dims)
{
	Oid			base = OidIsValid(type) ? getBaseType(type) : InvalidOid;
	Oid			element = OidIsValid(base) ? get_element_type(base) : InvalidOid;
	Shape	   *shape;

	if (OidIsValid(element))
	{
		shape = make_shape(SHAPE_ARRAY, type, nullable);
		if (dims > 1)
			shape->element = typed_shape_dims(type, false, dims - 1);
		else
		{
			shape->element = typed_shape_dims(element, true, 1);
			shape->element->guessed = true;
		}
		return shape;
	}
	if (is_composite_type(base))
	{
		shape = relation_row(get_typ_typrelid(base), type);
		shape->nullable = nullable;
		return shape;
	}
	return make_shape(is_json_type(type) ? SHAPE_UNKNOWN_JSON : SHAPE_SCALAR, type, nullable);
}

static Shape *
typed_shape(Oid type, bool nullable)
{
	return typed_shape_dims(type, nullable, 1);
}

static bool
name_in(const char *name, const char *const *names)
{
	for (int i = 0; names[i] != NULL; i++)
		if (strcmp(name, names[i]) == 0)
			return true;
	return false;
}

static Node *
strip_relabel(Node *node)
{
	while (node != NULL && IsA(node, RelabelType))
		node = (Node *) ((RelabelType *) node)->arg;
	return node;
}

static int
var_key(Var *var)
{
	return (var->varno << 16) | (var->varattno & 0xFFFF);
}

static const char *const comparison_operators[] = {
	"=", "<>", "<", ">", "<=", ">=", "~~", "!~~", "~~*", "!~~*", "~", "!~", "~*", "!~*",
	"@>", "<@", "&&", "?", "?|", "?&", NULL
};

static const char *const nonnull_operators[] = {
	"+", "-", "*", "/", "%", "^", "||", "=", "<>", "<", ">", "<=", ">=", "~~", "!~~", "~~*",
	"!~~*", "~", "!~", "~*", "!~*", "@>", "<@", "&&", "?", "?|", "?&", NULL
};

static const char *const nonnull_functions[] = {
	"lower", "upper", "initcap", "btrim", "ltrim", "rtrim", "length", "char_length",
	"character_length", "octet_length", "bit_length", "md5", "sha224", "sha256", "sha384",
	"sha512", "encode", "replace", "translate", "left", "right", "lpad", "rpad", "repeat",
	"reverse", "split_part", "substr", "strpos", "starts_with", "abs", "round", "trunc",
	"floor", "ceil", "ceiling", "sign", "mod", "power", "sqrt", "exp", "ln", "log", "date_trunc",
	"date_part", "extract", "to_char", "to_timestamp", "to_date", "age", "timezone",
	"make_date", "make_time", "make_timestamp", "make_timestamptz", "make_interval",
	"justify_days", "justify_hours", "justify_interval", "cardinality",
	"json_array_length", "jsonb_array_length", "json_typeof", "jsonb_typeof", "array_to_string",
	"quote_ident", "quote_literal", "to_hex", "chr", "ascii", NULL
};

static const char *const constant_functions[] = {
	"now", "statement_timestamp", "clock_timestamp", "transaction_timestamp",
	"gen_random_uuid", "uuidv4", "uuidv7", "random", "pi", "concat", "format", NULL
};

static const char *const nonnull_set_functions[] = {
	"generate_series", "generate_subscripts", NULL
};

static const char *const text_send_functions[] = {
	"textsend", "varcharsend", "bpcharsend", "namesend", "charsend", "enum_send", "xml_send",
	"unknownsend", "cstring_send", "citextsend", NULL
};

static void
collect_conjuncts(Node *node, List **out)
{
	if (node == NULL)
		return;
	if (IsA(node, BoolExpr) && ((BoolExpr *) node)->boolop == AND_EXPR)
	{
		ListCell   *lc;

		foreach(lc, ((BoolExpr *) node)->args)
			collect_conjuncts(lfirst(lc), out);
		return;
	}
	if (IsA(node, List))
	{
		ListCell   *lc;

		foreach(lc, (List *) node)
			collect_conjuncts(lfirst(lc), out);
		return;
	}
	*out = lappend(*out, node);
}

static void
refine_with_var(Scope *scope, Node *node)
{
	Var		   *var;

	node = strip_relabel(node);
	if (node == NULL || !IsA(node, Var))
		return;
	var = (Var *) node;
	if (var->varlevelsup != 0)
		return;
	scope->present = bms_add_member(scope->present, var->varno);
	scope->nonnull = lappend_int(scope->nonnull, var_key(var));
}

static void
refine_with_quals(Scope *scope, Node *quals)
{
	List	   *conjuncts = NIL;
	ListCell   *lc;

	collect_conjuncts(quals, &conjuncts);
	foreach(lc, conjuncts)
	{
		Node	   *qual = lfirst(lc);

		if (IsA(qual, NullTest) && ((NullTest *) qual)->nulltesttype == IS_NOT_NULL &&
			!((NullTest *) qual)->argisrow)
			refine_with_var(scope, (Node *) ((NullTest *) qual)->arg);
		else if (IsA(qual, OpExpr))
		{
			OpExpr	   *op = (OpExpr *) qual;
			char	   *opname = get_opname(op->opno);
			ListCell   *arg;

			if (opname == NULL || !name_in(opname, comparison_operators) || !func_strict(op->opfuncid))
				continue;
			foreach(arg, op->args)
				refine_with_var(scope, lfirst(arg));
		}
	}
}

static Scope *
make_scope(Query *query, Scope *parent)
{
	Scope	   *scope = palloc0(sizeof(Scope));

	scope->query = query;
	scope->parent = parent;
	if (query->jointree != NULL)
		refine_with_quals(scope, query->jointree->quals);
	return scope;
}

static Scope *
refined_scope(Scope *scope, Node *quals)
{
	Scope	   *child = palloc(sizeof(Scope));

	memcpy(child, scope, sizeof(Scope));
	child->present = bms_copy(scope->present);
	child->nonnull = list_copy(scope->nonnull);
	refine_with_quals(child, quals);
	return child;
}

static Shape *
attribute_shape(Oid relid, AttrNumber attno, Oid type)
{
	HeapTuple	tuple;
	bool		not_null = false;
	int			dims = 1;

	if (attno < 0)
		return typed_shape(type, false);
	tuple = SearchSysCache2(ATTNUM, ObjectIdGetDatum(relid), Int16GetDatum(attno));
	if (HeapTupleIsValid(tuple))
	{
		Form_pg_attribute attribute = (Form_pg_attribute) GETSTRUCT(tuple);

		not_null = attribute->attnotnull && !attribute->attisdropped;
		dims = Max(attribute->attndims, 1);
		ReleaseSysCache(tuple);
	}
	return typed_shape_dims(type, !not_null, dims);
}

static List *
target_entries(Query *query)
{
	List	   *entries = query->commandType == CMD_SELECT ? query->targetList : query->returningList;
	List	   *visible = NIL;
	ListCell   *lc;

	foreach(lc, entries)
	{
		TargetEntry *entry = lfirst_node(TargetEntry, lc);

		if (!entry->resjunk)
			visible = lappend(visible, entry);
	}
	return visible;
}

static Shape *
relation_row(Oid relid, Oid rowtype)
{
	Shape	   *shape = make_shape(SHAPE_OBJECT, rowtype, false);
	AttrNumber	attno = 1;

	for (;;)
	{
		HeapTuple	tuple = SearchSysCache2(ATTNUM, ObjectIdGetDatum(relid), Int16GetDatum(attno));
		Form_pg_attribute attribute;

		if (!HeapTupleIsValid(tuple))
			break;
		attribute = (Form_pg_attribute) GETSTRUCT(tuple);
		if (!attribute->attisdropped)
		{
			Field	   *field = palloc(sizeof(Field));

			field->name = pstrdup(NameStr(attribute->attname));
			field->shape = typed_shape_dims(attribute->atttypid, !attribute->attnotnull, Max(attribute->attndims, 1));
			shape->fields = lappend(shape->fields, field);
		}
		ReleaseSysCache(tuple);
		attno++;
	}
	return shape;
}

static Shape *shape_target(Scope *inner, Query *query, int index, TargetEntry *entry);

static Shape *
query_row(Scope *scope, Query *query, Oid rowtype)
{
	Scope	   *inner = make_scope(query, scope);
	Shape	   *shape = make_shape(SHAPE_OBJECT, rowtype, false);
	ListCell   *lc;
	int			index = 0;

	foreach(lc, target_entries(query))
	{
		TargetEntry *entry = lfirst_node(TargetEntry, lc);
		Field	   *field = palloc(sizeof(Field));

		field->name = pstrdup(entry->resname != NULL ? entry->resname : "?column?");
		field->shape = shape_target(inner, query, index++, entry);
		shape->fields = lappend(shape->fields, field);
	}
	return shape;
}

static Query *
find_cte(Scope **scope, RangeTblEntry *rte)
{
	ListCell   *lc;

	for (Index level = 0; level < rte->ctelevelsup && (*scope)->parent != NULL; level++)
		*scope = (*scope)->parent;
	foreach(lc, (*scope)->query->cteList)
	{
		CommonTableExpr *cte = lfirst_node(CommonTableExpr, lc);

		if (strcmp(cte->ctename, rte->ctename) == 0)
			return cte->cterecursive ? NULL : (Query *) cte->ctequery;
	}
	return NULL;
}

static Shape *
shape_column_of_query(Scope *scope, Query *query, AttrNumber attno, Oid type)
{
	TargetEntry *entry;
	Scope	   *inner;

	if (query == NULL)
		return guessed_shape(type);
	entry = list_nth_node(TargetEntry, target_entries(query), attno - 1);
	inner = make_scope(query, scope);
	return shape_target(inner, query, attno - 1, entry);
}

static Shape *merge_shapes(Shape *a, Shape *b, Oid type);

static Shape *
shape_setop(Scope *scope, Query *query, Node *node, int index, Oid type)
{
	if (IsA(node, RangeTblRef))
	{
		RangeTblEntry *rte = rt_fetch(((RangeTblRef *) node)->rtindex, query->rtable);

		if (rte->rtekind != RTE_SUBQUERY)
			return guessed_shape(type);
		return shape_column_of_query(scope, rte->subquery, index + 1, type);
	}
	if (IsA(node, SetOperationStmt))
	{
		SetOperationStmt *setop = (SetOperationStmt *) node;
		Shape	   *left = shape_setop(scope, query, setop->larg, index, type);
		Shape	   *right;
		Shape	   *merged;

		if (setop->op == SETOP_EXCEPT)
			return left;
		right = shape_setop(scope, query, setop->rarg, index, type);
		merged = merge_shapes(left, right, type);
		if (setop->op == SETOP_INTERSECT)
		{
			merged = copy_shape(merged);
			merged->nullable = left->nullable && right->nullable;
			merged->guessed = merged->nullable && (left->guessed || right->guessed);
		}
		return merged;
	}
	return guessed_shape(type);
}

static Shape *
shape_target(Scope *inner, Query *query, int index, TargetEntry *entry)
{
	if (query->setOperations != NULL)
		return shape_setop(inner, query, query->setOperations, index, exprType((Node *) entry->expr));
	return shape_expr(inner, (Node *) entry->expr);
}

static bool
always_one_row(Query *query)
{
	if (query == NULL || query->commandType != CMD_SELECT || query->setOperations != NULL ||
		query->hasTargetSRFs || query->havingQual != NULL || query->limitCount != NULL ||
		query->limitOffset != NULL || query->groupClause != NIL || query->groupingSets != NIL)
		return false;
	if (query->hasAggs)
		return true;
	return query->jointree != NULL && query->jointree->fromlist == NIL && query->jointree->quals == NULL;
}

static JoinExpr *
find_join(Node *node, int rtindex)
{
	ListCell   *lc;

	if (node == NULL)
		return NULL;
	if (IsA(node, FromExpr))
	{
		foreach(lc, ((FromExpr *) node)->fromlist)
		{
			JoinExpr   *found = find_join(lfirst(lc), rtindex);

			if (found != NULL)
				return found;
		}
		return NULL;
	}
	if (IsA(node, JoinExpr))
	{
		JoinExpr   *join = (JoinExpr *) node;
		JoinExpr   *found;

		if (join->rtindex == rtindex)
			return join;
		found = find_join(join->larg, rtindex);
		return found != NULL ? found : find_join(join->rarg, rtindex);
	}
	return NULL;
}

static bool
quals_always_true(Node *quals)
{
	List	   *conjuncts = NIL;
	ListCell   *lc;

	collect_conjuncts(quals, &conjuncts);
	foreach(lc, conjuncts)
	{
		Node	   *qual = lfirst(lc);

		if (!IsA(qual, Const) || ((Const *) qual)->constisnull || ((Const *) qual)->consttype != BOOLOID ||
			!DatumGetBool(((Const *) qual)->constvalue))
			return false;
	}
	return true;
}

static bool
never_null_extended(Query *query, Var *var)
{
	RangeTblEntry *rte = rt_fetch(var->varno, query->rtable);
	int			member = -1;

	if (rte->rtekind != RTE_SUBQUERY || !always_one_row(rte->subquery))
		return false;
	while ((member = bms_next_member(var->varnullingrels, member)) >= 0)
	{
		JoinExpr   *join = find_join((Node *) query->jointree, member);

		if (join == NULL || join->jointype != JOIN_LEFT || !IsA(join->rarg, RangeTblRef) ||
			((RangeTblRef *) join->rarg)->rtindex != var->varno || !quals_always_true(join->quals))
			return false;
	}
	return true;
}

static bool
nonnull_set_function(RangeTblEntry *rte, AttrNumber attno)
{
	RangeTblFunction *function;
	Node	   *expr;
	char	   *name;

	if (rte->rtekind != RTE_FUNCTION || list_length(rte->functions) != 1 || attno != 1)
		return false;
	function = linitial_node(RangeTblFunction, rte->functions);
	expr = function->funcexpr;
	if (expr == NULL || !IsA(expr, FuncExpr))
		return false;
	name = get_func_name(((FuncExpr *) expr)->funcid);
	return name != NULL && name_in(name, nonnull_set_functions);
}

static Shape *
shape_var(Scope *scope, Var *var)
{
	Scope	   *level = scope;
	RangeTblEntry *rte;
	Shape	   *base;
	Shape	   *result;
	bool		null_extended;

	for (Index i = 0; i < var->varlevelsup && level->parent != NULL; i++)
		level = level->parent;
	rte = rt_fetch(var->varno, level->query->rtable);

	if (var->varattno == 0)
	{
		if (rte->rtekind == RTE_RELATION)
			base = relation_row(rte->relid, var->vartype);
		else if (rte->rtekind == RTE_SUBQUERY)
			base = query_row(level, rte->subquery, var->vartype);
		else if (rte->rtekind == RTE_CTE)
		{
			Scope	   *cte_scope = level;
			Query	   *cte = find_cte(&cte_scope, rte);

			base = cte != NULL ? query_row(cte_scope, cte, var->vartype) : guessed_shape(var->vartype);
		}
		else
			base = guessed_shape(var->vartype);
	}
	else
	{
		switch (rte->rtekind)
		{
			case RTE_RELATION:
				base = attribute_shape(rte->relid, var->varattno, var->vartype);
				break;
			case RTE_FUNCTION:
				base = nonnull_set_function(rte, var->varattno) ||
					(rte->funcordinality && var->varattno == list_length(rte->eref->colnames))
					? typed_shape(var->vartype, false)
					: guessed_shape(var->vartype);
				break;
			case RTE_SUBQUERY:
				base = shape_column_of_query(level, rte->subquery, var->varattno, var->vartype);
				break;
			case RTE_CTE:
				{
					Scope	   *cte_scope = level;
					Query	   *cte = find_cte(&cte_scope, rte);

					base = shape_column_of_query(cte_scope, cte, var->varattno, var->vartype);
					break;
				}
			case RTE_JOIN:
				{
					Node	   *alias = list_nth(rte->joinaliasvars, var->varattno - 1);

					base = alias != NULL ? shape_expr(level, alias) : guessed_shape(var->vartype);
					break;
				}
			case RTE_GROUP:
				base = shape_expr(level, list_nth(rte->groupexprs, var->varattno - 1));
				break;
			case RTE_VALUES:
				{
					ListCell   *lc;

					base = make_shape(SHAPE_SCALAR, var->vartype, false);
					foreach(lc, rte->values_lists)
					{
						Shape	   *value = shape_expr(level, list_nth(lfirst(lc), var->varattno - 1));

						base->nullable = base->nullable || value->nullable;
						base->guessed = base->guessed || value->guessed;
					}
					break;
				}
			default:
				base = guessed_shape(var->vartype);
				break;
		}
	}

	result = copy_shape(base);
	if (list_member_int(level->nonnull, var_key(var)))
	{
		result->nullable = false;
		result->guessed = false;
		return result;
	}
	null_extended = !bms_is_empty(var->varnullingrels) && !bms_is_member(var->varno, level->present) &&
		!never_null_extended(level->query, var);
	result->nullable = result->nullable || null_extended;
	return result;
}

static Shape *
merge_shapes(Shape *a, Shape *b, Oid type)
{
	Shape	   *merged;

	if (a == NULL)
		return b;
	if (b == NULL)
		return a;
	if (a->null_only || b->null_only)
	{
		merged = copy_shape(a->null_only ? b : a);
		merged->nullable = true;
		if (OidIsValid(type))
			merged->type = type;
		return merged;
	}
	if (a->kind == SHAPE_ARRAY && b->kind == SHAPE_ARRAY)
	{
		merged = copy_shape(a);
		merged->element = merge_shapes(a->element, b->element, InvalidOid);
	}
	else if (a->kind == SHAPE_OBJECT && b->kind == SHAPE_OBJECT && b->fields == NIL)
		merged = copy_shape(a);
	else if (a->kind == SHAPE_OBJECT && b->kind == SHAPE_OBJECT && a->fields == NIL)
		merged = copy_shape(b);
	else if (a->kind == SHAPE_SCALAR && b->kind == SHAPE_SCALAR && a->type == b->type)
		merged = copy_shape(a);
	else
		merged = make_shape(is_json_type(type) ? SHAPE_UNKNOWN_JSON : SHAPE_SCALAR,
							OidIsValid(type) ? type : a->type, false);
	if (OidIsValid(type))
		merged->type = type;
	merged->json = a->json || b->json;
	merged->nullable = a->nullable || b->nullable;
	merged->guessed = a->guessed || b->guessed;
	return merged;
}

static char *
const_text(Const *constant)
{
	Oid			output;
	bool		varlena;

	getTypeOutputInfo(constant->consttype, &output, &varlena);
	return OidOutputFunctionCall(output, constant->constvalue);
}

static Shape *
shape_json_literal(Const *constant)
{
	char	   *text;

	if (constant->constisnull)
	{
		Shape	   *shape = make_shape(SHAPE_SCALAR, constant->consttype, true);

		shape->null_only = true;
		return shape;
	}
	text = const_text(constant);
	while (*text == ' ' || *text == '\n' || *text == '\t')
		text++;
	if (strncmp(text, "[]", 2) == 0)
	{
		Shape	   *shape = make_shape(SHAPE_ARRAY, constant->consttype, false);

		shape->json = true;
		return shape;
	}
	if (strncmp(text, "{}", 2) == 0)
	{
		Shape	   *shape = make_shape(SHAPE_OBJECT, constant->consttype, false);

		shape->json = true;
		return shape;
	}
	return make_shape(SHAPE_UNKNOWN_JSON, constant->consttype, false);
}

static bool
any_nullable(Scope *scope, List *args, bool *guessed)
{
	ListCell   *lc;
	bool		nullable = false;

	foreach(lc, args)
	{
		Shape	   *arg = shape_expr(scope, lfirst(lc));

		nullable = nullable || arg->nullable;
		*guessed = *guessed || arg->guessed;
	}
	return nullable;
}

static Shape *
as_json(Shape *shape, Oid type)
{
	Shape	   *result = copy_shape(shape);

	result->type = shape->kind == SHAPE_SCALAR ? shape->type : type;
	result->json = true;
	if (shape->kind == SHAPE_SCALAR && is_json_type(shape->type))
		result->kind = SHAPE_UNKNOWN_JSON;
	return result;
}

static Shape *
shape_build_object(Scope *scope, List *args, Oid type)
{
	Shape	   *shape = make_shape(SHAPE_OBJECT, type, false);

	shape->json = true;
	if (list_length(args) % 2 != 0)
		return make_shape(SHAPE_UNKNOWN_JSON, type, false);
	for (int i = 0; i + 1 < list_length(args); i += 2)
	{
		Node	   *key = strip_relabel(list_nth(args, i));
		Node	   *value = list_nth(args, i + 1);
		Field	   *field;

		if (key == NULL || !IsA(key, Const) || ((Const *) key)->constisnull)
			return make_shape(SHAPE_UNKNOWN_JSON, type, false);
		field = palloc(sizeof(Field));
		field->name = const_text((Const *) key);
		field->shape = shape_expr(scope, value);
		shape->fields = lappend(shape->fields, field);
	}
	return shape;
}

static Shape *
shape_build_array(Scope *scope, List *args, Oid type, bool skip_nulls)
{
	Shape	   *shape = make_shape(SHAPE_ARRAY, type, false);
	ListCell   *lc;

	shape->json = true;
	foreach(lc, args)
	{
		Shape	   *element = shape_expr(scope, lfirst(lc));

		if (skip_nulls)
		{
			element = copy_shape(element);
			element->nullable = false;
		}
		shape->element = merge_shapes(shape->element, element, InvalidOid);
	}
	return shape;
}

static Shape *
shape_func(Scope *scope, FuncExpr *func)
{
	char	   *name = get_func_name(func->funcid);
	Oid			type = func->funcresulttype;
	Shape	   *shape;
	bool		guessed = false;

	if (func->funcformat == COERCE_EXPLICIT_CAST || func->funcformat == COERCE_IMPLICIT_CAST)
	{
		Shape	   *arg = shape_expr(scope, linitial(func->args));

		shape = make_shape(SHAPE_SCALAR, type, arg->nullable);
		shape->guessed = arg->guessed;
		shape->cast_from = arg->kind == SHAPE_SCALAR ? arg->type : InvalidOid;
		return shape;
	}
	if (name == NULL)
		return guessed_shape(type);
	if (!func->funcvariadic && (strcmp(name, "json_build_object") == 0 || strcmp(name, "jsonb_build_object") == 0))
		return shape_build_object(scope, func->args, type);
	if (!func->funcvariadic && (strcmp(name, "json_build_array") == 0 || strcmp(name, "jsonb_build_array") == 0))
		return shape_build_array(scope, func->args, type, false);
	if (strcmp(name, "to_json") == 0 || strcmp(name, "to_jsonb") == 0 ||
		strcmp(name, "row_to_json") == 0 || strcmp(name, "array_to_json") == 0)
	{
		Shape	   *arg = shape_expr(scope, linitial(func->args));

		shape = as_json(arg, type);
		shape->nullable = arg->nullable;
		return shape;
	}
	if (name_in(name, constant_functions) || name_in(name, nonnull_set_functions))
		return typed_shape(type, false);
	if (strcmp(name, "concat_ws") == 0)
	{
		Shape	   *separator = shape_expr(scope, linitial(func->args));

		shape = make_shape(SHAPE_SCALAR, type, separator->nullable);
		shape->guessed = separator->guessed;
		return shape;
	}
	if (func_strict(func->funcid) && name_in(name, nonnull_functions))
	{
		shape = make_shape(SHAPE_SCALAR, type, any_nullable(scope, func->args, &guessed));
		shape->guessed = guessed;
		return shape;
	}
	if (is_json_type(type))
	{
		shape = make_shape(SHAPE_UNKNOWN_JSON, type, true);
		shape->guessed = true;
		return shape;
	}
	return guessed_shape(type);
}

static Shape *
shape_op(Scope *scope, OpExpr *op)
{
	char	   *name = get_opname(op->opno);
	Shape	   *shape;
	bool		guessed = false;

	if (name != NULL && func_strict(op->opfuncid) && name_in(name, nonnull_operators))
	{
		shape = make_shape(is_json_type(op->opresulttype) ? SHAPE_UNKNOWN_JSON : SHAPE_SCALAR,
						   op->opresulttype, any_nullable(scope, op->args, &guessed));
		shape->guessed = guessed;
		return shape;
	}
	shape = guessed_shape(op->opresulttype);
	if (is_json_type(op->opresulttype))
		shape->kind = SHAPE_UNKNOWN_JSON;
	return shape;
}

static Shape *
first_argument(Scope *scope, Aggref *agg)
{
	ListCell   *lc;

	foreach(lc, agg->args)
	{
		TargetEntry *entry = lfirst_node(TargetEntry, lc);

		if (!entry->resjunk)
			return shape_expr(scope, (Node *) entry->expr);
	}
	return NULL;
}

static Shape *
shape_agg(Scope *scope, Aggref *agg)
{
	static const char *const value_aggregates[] = {
		"sum", "avg", "min", "max", "string_agg", "bool_and", "bool_or", "every",
		"bit_and", "bit_or", "bit_xor", NULL
	};
	char	   *name = get_func_name(agg->aggfnoid);
	Query	   *query = scope->query;
	bool		may_be_empty = query->groupClause == NIL || query->groupingSets != NIL || agg->aggfilter != NULL;
	Scope	   *inner = agg->aggfilter != NULL ? refined_scope(scope, (Node *) agg->aggfilter) : scope;
	Shape	   *argument = agg->aggstar ? NULL : first_argument(inner, agg);
	Shape	   *shape;

	if (name == NULL)
		return guessed_shape(agg->aggtype);
	if (strcmp(name, "count") == 0)
		return make_shape(SHAPE_SCALAR, agg->aggtype, false);
	if (strcmp(name, "json_agg") == 0 || strcmp(name, "jsonb_agg") == 0 ||
		strcmp(name, "json_agg_strict") == 0 || strcmp(name, "jsonb_agg_strict") == 0 ||
		strcmp(name, "array_agg") == 0)
	{
		shape = make_shape(SHAPE_ARRAY, agg->aggtype, may_be_empty);
		shape->json = is_json_type(agg->aggtype);
		shape->element = argument != NULL ? copy_shape(argument) : guessed_shape(InvalidOid);
		if (strstr(name, "_strict") != NULL)
			shape->element->nullable = false;
		return shape;
	}
	if (name_in(name, value_aggregates) && argument != NULL)
	{
		shape = make_shape(SHAPE_SCALAR, agg->aggtype, may_be_empty || argument->nullable);
		shape->guessed = argument->guessed;
		return shape;
	}
	if (is_json_type(agg->aggtype))
	{
		shape = make_shape(SHAPE_UNKNOWN_JSON, agg->aggtype, true);
		shape->guessed = true;
		return shape;
	}
	return guessed_shape(agg->aggtype);
}

static Shape *
shape_sublink(Scope *scope, SubLink *sublink)
{
	Oid			type = exprType((Node *) sublink);
	Query	   *query = (Query *) sublink->subselect;
	Scope	   *inner;
	List	   *entries;
	Shape	   *value;
	Shape	   *shape;

	if (sublink->subLinkType == EXISTS_SUBLINK)
		return make_shape(SHAPE_SCALAR, type, false);
	if (sublink->subLinkType != EXPR_SUBLINK && sublink->subLinkType != ARRAY_SUBLINK)
		return guessed_shape(type);
	inner = make_scope(query, scope);
	entries = target_entries(query);
	if (entries == NIL)
		return guessed_shape(type);
	value = shape_expr(inner, (Node *) linitial_node(TargetEntry, entries)->expr);
	if (sublink->subLinkType == ARRAY_SUBLINK)
	{
		shape = make_shape(SHAPE_ARRAY, type, false);
		shape->element = value;
		return shape;
	}
	shape = copy_shape(value);
	shape->nullable = value->nullable || !always_one_row(query);
	return shape;
}

static Shape *
shape_json_constructor(Scope *scope, JsonConstructorExpr *constructor)
{
	Oid			type = exprType((Node *) constructor);
	List	   *args = NIL;
	ListCell   *lc;

	foreach(lc, constructor->args)
	{
		Node	   *arg = lfirst(lc);

		if (IsA(arg, JsonValueExpr))
			arg = (Node *) ((JsonValueExpr *) arg)->formatted_expr;
		args = lappend(args, arg);
	}
	switch (constructor->type)
	{
		case JSCTOR_JSON_OBJECT:
			if (constructor->absent_on_null)
				return make_shape(SHAPE_UNKNOWN_JSON, type, false);
			return shape_build_object(scope, args, type);
		case JSCTOR_JSON_ARRAY:
			return shape_build_array(scope, args, type, constructor->absent_on_null);
		case JSCTOR_JSON_ARRAYAGG:
			if (constructor->func != NULL && IsA(constructor->func, Aggref))
			{
				Shape	   *shape = shape_agg(scope, (Aggref *) constructor->func);

				shape->type = type;
				shape->json = true;
				if (constructor->absent_on_null && shape->element != NULL)
					shape->element->nullable = false;
				return shape;
			}
			break;
		default:
			break;
	}
	{
		Shape	   *shape = make_shape(SHAPE_UNKNOWN_JSON, type, true);

		shape->guessed = true;
		return shape;
	}
}

static Shape *
shape_expr(Scope *scope, Node *node)
{
	check_stack_depth();
	if (node == NULL)
		return guessed_shape(InvalidOid);

	switch (nodeTag(node))
	{
		case T_Var:
			return shape_var(scope, (Var *) node);
		case T_Const:
			{
				Const	   *constant = (Const *) node;

				Shape	   *shape;

				if (is_json_type(constant->consttype))
					return shape_json_literal(constant);
				shape = typed_shape(constant->consttype, constant->constisnull);
				shape->null_only = constant->constisnull;
				return shape;
			}
		case T_Param:
			return typed_shape(((Param *) node)->paramtype, false);
		case T_FuncExpr:
			return shape_func(scope, (FuncExpr *) node);
		case T_OpExpr:
			return shape_op(scope, (OpExpr *) node);
		case T_Aggref:
			return shape_agg(scope, (Aggref *) node);
		case T_SubLink:
			return shape_sublink(scope, (SubLink *) node);
		case T_JsonConstructorExpr:
			return shape_json_constructor(scope, (JsonConstructorExpr *) node);
		case T_RelabelType:
			{
				Shape	   *shape = copy_shape(shape_expr(scope, (Node *) ((RelabelType *) node)->arg));

				shape->type = ((RelabelType *) node)->resulttype;
				return shape;
			}
		case T_CoerceViaIO:
			{
				CoerceViaIO *coerce = (CoerceViaIO *) node;
				Shape	   *arg = shape_expr(scope, (Node *) coerce->arg);
				Shape	   *shape = make_shape(is_json_type(coerce->resulttype) ? SHAPE_UNKNOWN_JSON : SHAPE_SCALAR,
											   coerce->resulttype, arg->nullable);

				shape->guessed = arg->guessed;
				shape->cast_from = arg->kind == SHAPE_SCALAR ? arg->type : InvalidOid;
				return shape;
			}
		case T_CoerceToDomain:
			{
				Shape	   *shape = copy_shape(shape_expr(scope, (Node *) ((CoerceToDomain *) node)->arg));

				shape->type = ((CoerceToDomain *) node)->resulttype;
				return shape;
			}
		case T_ArrayCoerceExpr:
			{
				Shape	   *shape = copy_shape(shape_expr(scope, (Node *) ((ArrayCoerceExpr *) node)->arg));

				shape->type = ((ArrayCoerceExpr *) node)->resulttype;
				return shape;
			}
		case T_CollateExpr:
			return shape_expr(scope, (Node *) ((CollateExpr *) node)->arg);
		case T_CoalesceExpr:
			{
				CoalesceExpr *coalesce = (CoalesceExpr *) node;
				Shape	   *merged = NULL;
				bool		nullable = true;
				bool		guessed = false;
				ListCell   *lc;

				foreach(lc, coalesce->args)
				{
					Shape	   *arg = shape_expr(scope, lfirst(lc));

					if (!arg->nullable)
						nullable = false;
					guessed = guessed || arg->guessed;
					merged = merge_shapes(merged, arg, coalesce->coalescetype);
				}
				merged = copy_shape(merged);
				merged->nullable = nullable;
				merged->guessed = nullable && guessed;
				return merged;
			}
		case T_CaseExpr:
			{
				CaseExpr   *expr = (CaseExpr *) node;
				Shape	   *merged = NULL;
				List	   *negated = NIL;
				ListCell   *lc;

				foreach(lc, expr->args)
				{
					CaseWhen   *when = lfirst_node(CaseWhen, lc);
					Scope	   *branch = expr->arg == NULL
						? refined_scope(scope, (Node *) lappend(list_copy(negated), when->expr))
						: scope;

					merged = merge_shapes(merged, shape_expr(branch, (Node *) when->result), expr->casetype);
					if (expr->arg == NULL && IsA(when->expr, NullTest) &&
						((NullTest *) when->expr)->nulltesttype == IS_NULL && !((NullTest *) when->expr)->argisrow)
					{
						NullTest   *not_null = copyObject((NullTest *) when->expr);

						not_null->nulltesttype = IS_NOT_NULL;
						negated = lappend(negated, not_null);
					}
				}
				merged = merge_shapes(merged, expr->defresult != NULL
									  ? shape_expr(refined_scope(scope, (Node *) negated), (Node *) expr->defresult)
									  : make_shape(SHAPE_SCALAR, expr->casetype, true), expr->casetype);
				return merged;
			}
		case T_MinMaxExpr:
			{
				MinMaxExpr *expr = (MinMaxExpr *) node;
				Shape	   *shape = make_shape(SHAPE_SCALAR, expr->minmaxtype, true);
				ListCell   *lc;

				foreach(lc, expr->args)
				{
					Shape	   *arg = shape_expr(scope, lfirst(lc));

					if (!arg->nullable)
						shape->nullable = false;
				}
				return shape;
			}
		case T_BoolExpr:
			{
				bool		guessed = false;
				Shape	   *shape = make_shape(SHAPE_SCALAR, BOOLOID, any_nullable(scope, ((BoolExpr *) node)->args, &guessed));

				shape->guessed = guessed;
				return shape;
			}
		case T_ScalarArrayOpExpr:
			{
				bool		guessed = false;
				Shape	   *shape = make_shape(SHAPE_SCALAR, BOOLOID, any_nullable(scope, ((ScalarArrayOpExpr *) node)->args, &guessed));

				shape->guessed = guessed;
				return shape;
			}
		case T_NullTest:
		case T_BooleanTest:
		case T_DistinctExpr:
			return make_shape(SHAPE_SCALAR, BOOLOID, false);
		case T_NullIfExpr:
			return make_shape(SHAPE_SCALAR, ((NullIfExpr *) node)->opresulttype, true);
		case T_SQLValueFunction:
			return make_shape(SHAPE_SCALAR, ((SQLValueFunction *) node)->type, false);
		case T_ArrayExpr:
			{
				ArrayExpr  *array = (ArrayExpr *) node;
				Shape	   *shape = make_shape(SHAPE_ARRAY, array->array_typeid, false);
				ListCell   *lc;

				foreach(lc, array->elements)
					shape->element = merge_shapes(shape->element, shape_expr(scope, lfirst(lc)), array->element_typeid);
				return shape;
			}
		case T_RowExpr:
			{
				RowExpr    *row = (RowExpr *) node;
				Shape	   *shape = make_shape(SHAPE_OBJECT, row->row_typeid, false);
				ListCell   *lc;
				int			position = 0;

				foreach(lc, row->args)
				{
					Field	   *field = palloc(sizeof(Field));

					position++;
					field->name = row->colnames != NIL && position <= list_length(row->colnames)
						? pstrdup(strVal(list_nth(row->colnames, position - 1)))
						: psprintf("f%d", position);
					field->shape = shape_expr(scope, lfirst(lc));
					shape->fields = lappend(shape->fields, field);
				}
				return shape;
			}
		case T_WindowFunc:
			{
				static const char *const ranking[] = {
					"row_number", "rank", "dense_rank", "percent_rank", "cume_dist", "ntile", "count", NULL
				};
				WindowFunc *window = (WindowFunc *) node;
				char	   *name = get_func_name(window->winfnoid);

				if (name != NULL && name_in(name, ranking))
					return make_shape(SHAPE_SCALAR, window->wintype, false);
				return guessed_shape(window->wintype);
			}
		default:
			{
				Oid			type = exprType(node);
				Shape	   *shape = guessed_shape(type);

				if (is_json_type(type))
					shape->kind = SHAPE_UNKNOWN_JSON;
				return shape;
			}
	}
}

static bool
has_array_codec(Oid type)
{
	switch (type)
	{
		case BOOLOID: case BYTEAOID: case NAMEOID: case INT8OID: case INT2OID: case INT4OID:
		case TEXTOID: case OIDOID: case JSONOID: case CIDROID: case FLOAT4OID: case FLOAT8OID:
		case INETOID: case BPCHAROID: case VARCHAROID: case DATEOID: case TIMEOID:
		case TIMESTAMPOID: case TIMESTAMPTZOID: case INTERVALOID: case TIMETZOID:
		case NUMERICOID: case REGCLASSOID: case UUIDOID: case JSONBOID:
			return true;
		default:
			return false;
	}
}

static int
compare_enum(const void *a, const void *b)
{
	float4		left = (*(Form_pg_enum const *) a)->enumsortorder;
	float4		right = (*(Form_pg_enum const *) b)->enumsortorder;

	return left < right ? -1 : left > right ? 1 : 0;
}

static void
append_quoted(StringInfo out, const char *text)
{
	appendStringInfoChar(out, '"');
	for (const char *c = text; *c != '\0'; c++)
	{
		if (*c == '"' || *c == '\\')
			appendStringInfoChar(out, '\\');
		appendStringInfoChar(out, *c);
	}
	appendStringInfoChar(out, '"');
}

static bool
append_enum(StringInfo out, Oid type)
{
	CatCList   *list;
	Form_pg_enum *labels;

	if (get_typtype(type) != TYPTYPE_ENUM)
		return false;
	list = SearchSysCacheList1(ENUMTYPOIDNAME, ObjectIdGetDatum(type));
	labels = palloc(sizeof(Form_pg_enum) * Max(list->n_members, 1));
	for (int i = 0; i < list->n_members; i++)
		labels[i] = (Form_pg_enum) GETSTRUCT(&list->members[i]->tuple);
	qsort(labels, list->n_members, sizeof(Form_pg_enum), compare_enum);
	appendStringInfoString(out, "Schema.Literals([");
	for (int i = 0; i < list->n_members; i++)
	{
		if (i > 0)
			appendStringInfoString(out, ", ");
		append_quoted(out, NameStr(labels[i]->enumlabel));
	}
	appendStringInfoString(out, "])");
	ReleaseSysCacheList(list);
	return true;
}

static void
add_note(char **note, const char *text)
{
	*note = *note == NULL ? pstrdup(text) : psprintf("%s; %s", *note, text);
}

static void
append_scalar(StringInfo out, Shape *shape, bool in_json, char **note)
{
	Oid			type = getBaseType(shape->type);

	if (append_enum(out, type))
		return;
	if (type == TEXTOID && OidIsValid(shape->cast_from) && getBaseType(shape->cast_from) == INT8OID)
	{
		appendStringInfoString(out, "Schema.BigIntFromString");
		return;
	}
	if (is_json_type(type))
	{
		appendStringInfoString(out, "Schema.Unknown");
		add_note(note, "json with unknown structure");
		return;
	}
	if (in_json)
	{
		switch (type)
		{
			case BOOLOID:
				appendStringInfoString(out, "Schema.Boolean");
				return;
			case INT8OID:
				appendStringInfoString(out, "Schema.Int.pipe(Schema.decodeTo(Schema.BigInt, { decode: SchemaGetter.BigInt(), encode: SchemaGetter.Number() }))");
				add_note(note, "JSON number decoded to a bigint, values beyond 2^53 fail to decode, cast to ::text for the full range");
				return;
			case NUMERICOID:
				appendStringInfoString(out, "Schema.Number");
				add_note(note, "JSON number can lose precision, cast to ::text");
				return;
			case INT2OID: case INT4OID: case FLOAT4OID: case FLOAT8OID: case OIDOID:
				appendStringInfoString(out, "Schema.Number");
				return;
			case TIMESTAMPTZOID:
				appendStringInfoString(out, "Schema.DateFromString");
				return;
			case TIMESTAMPOID:
				appendStringInfoString(out, "Schema.String");
				add_note(note, "timestamp without time zone, use timestamptz to decode as a Date");
				return;
			default:
				appendStringInfoString(out, "Schema.String");
				return;
		}
	}
	switch (type)
	{
		case BOOLOID:
			appendStringInfoString(out, "Schema.Boolean");
			return;
		case INT2OID: case INT4OID: case FLOAT4OID: case FLOAT8OID: case OIDOID: case REGCLASSOID:
			appendStringInfoString(out, "Schema.Number");
			return;
		case INT8OID:
			appendStringInfoString(out, "Schema.BigInt");
			return;
		case TIMEOID:
			appendStringInfoString(out, "Schema.BigInt");
			add_note(note, "time is decoded as microseconds");
			return;
		case TIMESTAMPOID:
		case TIMESTAMPTZOID:
			appendStringInfoString(out, "Schema.Date");
			return;
		case BYTEAOID:
			appendStringInfoString(out, "Schema.Uint8Array");
			return;
		case INTERVALOID:
			appendStringInfoString(out, "Schema.Unknown");
			add_note(note, "interval is decoded as { months, days, microseconds }");
			return;
		case NUMERICOID:
			appendStringInfoString(out, "Schema.String");
			add_note(note, "numeric is decoded as a decimal string");
			return;
		default:
			appendStringInfoString(out, "Schema.String");
			return;
	}
}

static bool
has_scalar_codec(Oid type)
{
	switch (type)
	{
		case BOOLOID: case BPCHAROID: case BYTEAOID: case CIDROID: case DATEOID: case FLOAT4OID:
		case FLOAT8OID: case INETOID: case INT2OID: case INT4OID: case INT8OID: case INTERVALOID:
		case JSONOID: case JSONBOID: case NAMEOID: case NUMERICOID: case OIDOID: case REGCLASSOID:
		case TEXTOID: case TIMEOID: case TIMESTAMPOID: case TIMESTAMPTZOID: case TIMETZOID:
		case UUIDOID: case VARCHAROID:
			return true;
		default:
			return false;
	}
}

static bool
binary_output_is_text(Oid type)
{
	HeapTuple	tuple = SearchSysCache1(TYPEOID, ObjectIdGetDatum(type));
	Oid			send = InvalidOid;
	char	   *name;

	if (HeapTupleIsValid(tuple))
	{
		send = ((Form_pg_type) GETSTRUCT(tuple))->typsend;
		ReleaseSysCache(tuple);
	}
	if (!OidIsValid(send))
		return false;
	name = get_func_name(send);
	return name != NULL && name_in(name, text_send_functions);
}

static bool
driver_decodes_scalar(Oid type)
{
	Oid			base = getBaseType(type);

	return has_scalar_codec(base) || get_typtype(base) == TYPTYPE_ENUM || binary_output_is_text(base);
}

static char *
undecodable_reason(Shape *shape, bool in_json)
{
	Oid			element;

	if (in_json || shape->json || !OidIsValid(shape->type))
		return NULL;
	switch (shape->kind)
	{
		case SHAPE_OBJECT:
			return psprintf("@effect/sql-pg cannot decode %s, select it as ::text or wrap it in to_json",
							format_type_be(shape->type));
		case SHAPE_ARRAY:
			if (shape->element != NULL && shape->element->kind == SHAPE_ARRAY)
				return pstrdup("@effect/sql-pg cannot decode multidimensional arrays, select it as ::text or wrap it in to_json");
			element = get_element_type(getBaseType(shape->type));
			if (OidIsValid(element) && !has_array_codec(element))
				return psprintf("@effect/sql-pg cannot decode %s, select it as ::text or wrap it in to_json",
								format_type_be(shape->type));
			return NULL;
		case SHAPE_SCALAR:
			if (!driver_decodes_scalar(shape->type))
				return psprintf("@effect/sql-pg cannot decode %s, select it as ::text",
								format_type_be(shape->type));
			return NULL;
		default:
			return NULL;
	}
}

static bool
valid_identifier(const char *name)
{
	if (!(isalpha((unsigned char) name[0]) || name[0] == '_' || name[0] == '$'))
		return false;
	for (const char *c = name; *c != '\0'; c++)
		if (!(isalnum((unsigned char) *c) || *c == '_' || *c == '$'))
			return false;
	return true;
}

static void
append_indent(StringInfo out, int depth)
{
	for (int i = 0; i < depth; i++)
		appendStringInfoString(out, "  ");
}

static void
append_schema(StringInfo out, Shape *shape, bool in_json, int depth, bool pretty)
{
	char	   *ignored = NULL;
	bool		child_json = in_json || shape->json || is_json_type(shape->type);

	if (shape->nullable)
		appendStringInfoString(out, "Schema.NullOr(");
	if (shape->kind != SHAPE_SCALAR && undecodable_reason(shape, in_json) != NULL)
	{
		appendStringInfoString(out, "Schema.String");
		if (shape->nullable)
			appendStringInfoChar(out, ')');
		return;
	}
	switch (shape->kind)
	{
		case SHAPE_OBJECT:
			if (shape->fields == NIL)
			{
				appendStringInfoString(out, "Schema.Struct({})");
				break;
			}
			appendStringInfoString(out, "Schema.Struct({");
			{
				ListCell   *lc;

				foreach(lc, shape->fields)
				{
					Field	   *field = lfirst(lc);

					if (pretty)
					{
						appendStringInfoChar(out, '\n');
						append_indent(out, depth + 1);
					}
					else
						appendStringInfoString(out, lc == list_head(shape->fields) ? " " : ", ");
					if (valid_identifier(field->name))
						appendStringInfoString(out, field->name);
					else
						append_quoted(out, field->name);
					appendStringInfoString(out, ": ");
					append_schema(out, field->shape, child_json, depth + 1, pretty);
					if (pretty)
						appendStringInfoChar(out, ',');
				}
				if (pretty)
				{
					appendStringInfoChar(out, '\n');
					append_indent(out, depth);
				}
				else
					appendStringInfoChar(out, ' ');
			}
			appendStringInfoString(out, "})");
			break;
		case SHAPE_ARRAY:
			appendStringInfoString(out, "Schema.Array(");
			if (shape->element == NULL)
				appendStringInfoString(out, "Schema.Never");
			else
				append_schema(out, shape->element, child_json, depth, pretty);
			appendStringInfoChar(out, ')');
			break;
		case SHAPE_UNKNOWN_JSON:
			appendStringInfoString(out, "Schema.Unknown");
			break;
		case SHAPE_SCALAR:
			append_scalar(out, shape, in_json || shape->json, &ignored);
			break;
	}
	if (shape->nullable)
		appendStringInfoChar(out, ')');
}

static char *
describe_type(Shape *shape, bool in_json)
{
	char	   *name;

	if (shape->kind == SHAPE_OBJECT && (in_json || shape->json))
		return pstrdup("json object");
	if (shape->kind == SHAPE_ARRAY && (in_json || shape->json || is_json_type(shape->type)))
		return pstrdup("json array");
	if (!OidIsValid(shape->type))
		return pstrdup("unknown");
	name = format_type_be(shape->type);
	if (shape->kind == SHAPE_SCALAR && (in_json || shape->json) && !is_json_type(shape->type))
		return psprintf("%s in json", name);
	return name;
}

static void
collect_rows(List **rows, const char *path, Shape *shape, bool in_json)
{
	Row		   *row = palloc0(sizeof(Row));
	StringInfoData schema;
	bool		child_json = in_json || shape->json || is_json_type(shape->type);
	char	   *reason;

	initStringInfo(&schema);
	append_schema(&schema, shape, in_json, 0, false);
	row->path = pstrdup(path);
	row->pg_type = describe_type(shape, in_json);
	row->nullable = shape->nullable;
	row->schema = schema.data;
	if (shape->kind == SHAPE_SCALAR)
	{
		StringInfoData ignored;

		initStringInfo(&ignored);
		append_scalar(&ignored, shape, in_json || shape->json, &row->note);
	}
	reason = undecodable_reason(shape, in_json);
	if (reason != NULL)
		add_note(&row->note, reason);
	if (shape->guessed)
		add_note(&row->note, "nullability unknown, assumed nullable");
	*rows = lappend(*rows, row);
	if (reason != NULL)
		return;

	if (shape->kind == SHAPE_OBJECT && child_json)
	{
		ListCell   *lc;

		foreach(lc, shape->fields)
		{
			Field	   *field = lfirst(lc);

			collect_rows(rows, psprintf("%s.%s", path, field->name), field->shape, child_json);
		}
	}
	else if (shape->kind == SHAPE_ARRAY && shape->element != NULL)
		collect_rows(rows, psprintf("%s[]", path), shape->element, child_json);
}

static Query *
analyze_query(text *source, Oid **param_types, int *param_count)
{
	char	   *sql = text_to_cstring(source);
	List	   *statements = raw_parser(sql, RAW_PARSE_DEFAULT);
	Query	   *query;

	if (list_length(statements) != 1)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("query_schema expects exactly one statement")));
	*param_types = NULL;
	*param_count = 0;
	query = parse_analyze_varparams(linitial_node(RawStmt, statements), sql, param_types, param_count, NULL);
	if (query->commandType == CMD_UTILITY)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("query_schema only describes SELECT, INSERT, UPDATE, DELETE and MERGE")));
	if (query->commandType == CMD_SELECT)
	{
		List	   *rewritten = QueryRewrite(query);

		if (list_length(rewritten) == 1)
			query = linitial_node(Query, rewritten);
	}
	return query;
}

static Shape *
describe_row(Query *query)
{
	Scope	   *scope = make_scope(query, NULL);
	Shape	   *row = make_shape(SHAPE_OBJECT, RECORDOID, false);
	ListCell   *lc;
	int			index = 0;

	foreach(lc, target_entries(query))
	{
		TargetEntry *entry = lfirst_node(TargetEntry, lc);
		Field	   *field = palloc(sizeof(Field));

		field->name = pstrdup(entry->resname != NULL ? entry->resname : "?column?");
		field->shape = shape_target(scope, query, index++, entry);
		row->fields = lappend(row->fields, field);
	}
	return row;
}

PG_FUNCTION_INFO_V1(query_schema);

Datum
query_schema(PG_FUNCTION_ARGS)
{
	Oid		   *param_types;
	int			param_count;
	Query	   *query = analyze_query(PG_GETARG_TEXT_PP(0), &param_types, &param_count);
	Shape	   *row = describe_row(query);
	StringInfoData out;
	ListCell   *lc;

	initStringInfo(&out);
	appendStringInfoString(&out, "Schema.Struct({");
	foreach(lc, row->fields)
	{
		Field	   *field = lfirst(lc);
		char	   *reason = undecodable_reason(field->shape, false);

		if (reason != NULL)
			ereport(WARNING,
					(errmsg("column \"%s\": %s", field->name, reason)));

		appendStringInfoString(&out, "\n  ");
		if (valid_identifier(field->name))
			appendStringInfoString(&out, field->name);
		else
			append_quoted(&out, field->name);
		appendStringInfoString(&out, ": ");
		append_schema(&out, field->shape, false, 1, true);
		appendStringInfoChar(&out, ',');
	}
	appendStringInfoString(&out, row->fields == NIL ? "})" : "\n})");
	PG_RETURN_TEXT_P(cstring_to_text(out.data));
}

PG_FUNCTION_INFO_V1(query_shape);

Datum
query_shape(PG_FUNCTION_ARGS)
{
	ReturnSetInfo *result = (ReturnSetInfo *) fcinfo->resultinfo;
	Oid		   *param_types;
	int			param_count;
	Query	   *query;
	Shape	   *row;
	List	   *rows = NIL;
	ListCell   *lc;

	InitMaterializedSRF(fcinfo, 0);
	query = analyze_query(PG_GETARG_TEXT_PP(0), &param_types, &param_count);
	row = describe_row(query);

	for (int i = 0; i < param_count; i++)
	{
		Row		   *param = palloc0(sizeof(Row));
		StringInfoData schema;
		Shape	   *shape = make_shape(SHAPE_SCALAR, param_types[i], false);

		initStringInfo(&schema);
		append_scalar(&schema, shape, false, &param->note);
		param->path = psprintf("$%d", i + 1);
		param->pg_type = OidIsValid(param_types[i]) ? format_type_be(param_types[i]) : pstrdup("unknown");
		param->schema = schema.data;
		rows = lappend(rows, param);
	}
	foreach(lc, row->fields)
	{
		Field	   *field = lfirst(lc);

		collect_rows(&rows, field->name, field->shape, false);
	}

	foreach(lc, rows)
	{
		Row		   *item = lfirst(lc);
		Datum		values[5];
		bool		nulls[5] = {false, false, false, false, false};

		values[0] = CStringGetTextDatum(item->path);
		values[1] = CStringGetTextDatum(item->pg_type);
		values[2] = BoolGetDatum(item->nullable);
		values[3] = CStringGetTextDatum(item->schema);
		if (item->note != NULL)
			values[4] = CStringGetTextDatum(item->note);
		else
			nulls[4] = true;
		if (item->path[0] == '$')
			nulls[2] = true;
		tuplestore_putvalues(result->setResult, result->setDesc, values, nulls);
	}
	return (Datum) 0;
}
