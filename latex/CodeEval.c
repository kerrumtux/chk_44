#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include "objects.h"
#include "symbols.h"
#include "parser.h"
#include "eval.h"
#include "arith.h"

object_t t;
object_t nil;
symbol_t *quote_sym;
symbol_t *backquote_sym;
symbol_t *lambda_sym;
symbol_t *cond_sym;
symbol_t *defun_sym;
symbol_t *defmacro_sym;
symbol_t *setq_sym;
symbol_t *or_sym;
symbol_t *and_sym;
symbol_t *t_sym;
symbol_t *nil_sym;
symbol_t *rest_sym;
symbol_t *tagbody_sym;
symbol_t *block_sym;
symbol_t *return_from_sym;
symbol_t *labels_sym;
symbol_t *progn_sym;
object_t current_env = NULLOBJ;
jmp_buf repl_buf;
jmp_buf block_buf;

object_t eq(object_t list)
{
    if (list == NULLOBJ)
	error("eq: no args");
    if (TAIL(list) == NULLOBJ)
	error("eq: one arg");
    if (TAIL(TAIL(list)) != NULLOBJ)
	error("eq: too many args");
    object_t p1 = FIRST(list);
    object_t p2 = SECOND(list);
    if (p1 == p2)
	return t;
    else
	return nil;
}

object_t atom(object_t list)
{
    if (list == NULLOBJ)
	error("atom: no args");
    else if (TAIL(list) != NULLOBJ)
	error("atom: many args");
    object_t obj = FIRST(list);
    if (obj == NULLOBJ || TYPE(obj) != PAIR)
	return t;
    else
	return nil;
}

object_t quote(object_t list)
{
    if (TAIL(list) != NULLOBJ)
 	error("quote: many args");
    return FIRST(list);
}

void append_env(object_t l1, object_t l2);

object_t backquote_rec(object_t list)
{
    if (list == NULLOBJ)
 	return NULLOBJ;
    object_t o;
    if (TYPE(list) == NUMBER || TYPE(list) == BIGNUMBER)
	return new_number(get_value(list));
    else if (TYPE(list) == SYMBOL)
	return NEW_SYMBOL(GET_SYMBOL(list)->str);
    else if (TYPE(list) == ARRAY) {
 	array_t *arr = new_empty_array(GET_ARRAY(list)->length);
 	int l = GET_ARRAY(list)->length;
 	for (int i = 0; i < l; i++)
 	    arr->data[i] = backquote_rec(GET_ARRAY(list)->data[i]);
 	return NEW_OBJECT(ARRAY, arr);
    } else if (TYPE(list) == STRING)
	return NEW_STRING(GET_STRING(list)->data);
    else if (TYPE(list) == PAIR) {
 	object_t el = FIRST(list);
 	if (el == NULLOBJ)
 	    return new_pair(NULLOBJ, backquote_rec(TAIL(list)));
 	if (TYPE(el) == SYMBOL && !strcmp(GET_SYMBOL(el)->str, "BACKQUOTE"))
 	    return list;
 	if (TYPE(el) == SYMBOL && !strcmp(GET_SYMBOL(el)->str, "COMMA"))
 	    return eval(SECOND(list), current_env);
 	object_t first = backquote_rec(el);
 	if (first != NULLOBJ && TYPE(first) == PAIR) {
 	    object_t comma_at = FIRST(first);
 	    if (comma_at != NULLOBJ && TYPE(comma_at) == SYMBOL && !strcmp(GET_SYMBOL(comma_at)->str, "COMMA-AT")) {
 		object_t l = eval(SECOND(first), current_env);
 		if (l == NULLOBJ)
 		    return backquote_rec(TAIL(list));
 		if (TYPE(l) != PAIR)
		    error("COMMA-AT: not list");
 		object_t new_comma = backquote_rec(l);
 		append_env(new_comma, backquote_rec(TAIL(list)));
 		return new_comma;
 	    }
 	}
 	object_t tail = backquote_rec(TAIL(list));
 	return new_pair(first, tail);
    }
    error("backqoute: unknown type: %d\n", TYPE(list));
}

object_t backquote(object_t list)
{
    if (list == NULLOBJ)
 	error("backquote: NULLOBJ");
    return backquote_rec(FIRST(list));
}

object_t cond(object_t obj)
{
    if (obj == NULLOBJ)
	error("NULLOBJ in COND");
    object_t pair = FIRST(obj);
    if (TAIL(pair) == NULLOBJ)
	error("cond: not enough params");
    if (TAIL(TAIL(pair)) != NULLOBJ)
	error("cond: too many params");
    object_t p = FIRST(pair);
    if (eval(p, current_env) == t)
	return eval(SECOND(pair), current_env);
    else
	return cond(TAIL(obj));
}

object_t defun(object_t obj)
{
    symbol_t *name = find_symbol(GET_SYMBOL(FIRST(obj))->str);
    name->lambda = new_pair(NEW_SYMBOL("LAMBDA"), TAIL(obj));
    return NEW_SYMBOL(name->str);
}

object_t defmacro(object_t obj)
{
    symbol_t *name = find_symbol(GET_SYMBOL(FIRST(obj))->str);
    name->macro = new_pair(NEW_SYMBOL("LAMBDA"), TAIL(obj));
    return NEW_SYMBOL(name->str);
}

object_t progn(object_t params)
{
    if (params == NULLOBJ)
 	error("progn: params = NULLOBJ");
    object_t obj = eval(FIRST(params), current_env);
    if (TAIL(params) == NULLOBJ)
	return obj;
    return progn(TAIL(params));
}

int check_params(object_t list)
{
    if (list == NULLOBJ)
 	return 1;
    if (TYPE(FIRST(list)) != SYMBOL)
	return 0;
    return check_params(TAIL(list));
}

int is_lambda(object_t list)
{
    object_t lambda = FIRST(list);
    if (TYPE(lambda) != SYMBOL || GET_SYMBOL(lambda) != lambda_sym)
	error("Invalid lambda symbol");
    if (TAIL(list) == NULLOBJ)
	error("No params in lambda");
    object_t params = SECOND(list);
    if (params != NULLOBJ && TYPE(params) != PAIR)
	error("Invalid params in lambda");
    if (!check_params(params))
	error("Not symbol in lambda attrs");
    if (TAIL(TAIL(list)) == NULLOBJ)
	error("No body in lambda");
    return 1;
}

object_t make_env(object_t args, object_t values)
{
    if (args != NULLOBJ && values == NULLOBJ && GET_SYMBOL(FIRST(args)) != rest_sym)
	error("Not enough values for params");
    if (args == NULLOBJ && values != NULLOBJ)
	error("Invalid number of arguments");
    if (args == NULLOBJ)
	return NULLOBJ;
    object_t param = FIRST(args);
    if (GET_SYMBOL(param) == rest_sym) {
	if (TAIL(args) == NULLOBJ)
	    error("Missing parameter after &rest");
	if (TAIL(TAIL(args)) != NULLOBJ)
	    error("Too many parameters after &rest");
	return new_pair(new_pair(SECOND(args), values), nil);
    }
    object_t val = FIRST(values);
    object_t pair = new_pair(param, val);
    object_t new_env = make_env(TAIL(args), TAIL(values));
    return new_pair(pair, new_env);
}

int find_in_env(object_t env, object_t sym, object_t *res)
{
    if (env == NULLOBJ)
 	return 0;
    object_t pair = FIRST(env);
    object_t var = FIRST(pair);
    if (GET_SYMBOL(var)  == GET_SYMBOL(sym)){
 	*res = TAIL(pair);
 	return 1;
    } else
 	return find_in_env(TAIL(env), sym, res);
}

void append_env(object_t l1, object_t l2)
{
    while (GET_PAIR(l1)->right != NULLOBJ)
 	l1 = GET_PAIR(l1)->right;
    GET_PAIR(l1)->right = l2;
}

object_t eval_func(object_t lambda, object_t args, object_t env)
{
    object_t new_env = make_env(SECOND(lambda), args);
    object_t body;
    if (GET_PAIR(TAIL(TAIL(lambda)))->right == NULLOBJ)
 	body = THIRD(lambda);
    else
 	body = new_pair(NEW_SYMBOL("PROGN"), TAIL(TAIL(lambda)));
    if (new_env == NULLOBJ)
 	new_env = env;
    else
 	append_env(new_env, env);
    return eval(body, new_env);
}

object_t macro_call(object_t macro, object_t args, object_t env)
{
    object_t new_env = make_env(SECOND(macro), args);
    object_t body;
    object_t eval_res;
    body = TAIL(TAIL(macro));
    append_env(new_env, env);
    while (body != NULLOBJ) {
 	eval_res = eval(FIRST(body), new_env);
 	eval_res = eval(eval_res, new_env);
 	body = TAIL(body);
    }
    return eval_res;
}

object_t eval_args(object_t args, object_t env)
{
    if (args == NULLOBJ)
 	return NULLOBJ;
    object_t f = FIRST(args);
    object_t arg = eval(f, env);
    object_t tail = eval_args(TAIL(args), env);
    return new_pair(arg, tail);
}

int is_special_form(symbol_t *s)
{
    return s == quote_sym || s == defun_sym || s == defmacro_sym
	|| s == setq_sym || s == backquote_sym || s == cond_sym
	|| s == or_sym || s == and_sym || s == return_from_sym
	|| s == labels_sym || s == tagbody_sym || s == progn_sym;
}

object_t eval_symbol(object_t obj)
{
    object_t res;

    if (find_in_env(current_env, obj, &res))
	return res;
    else {
 	symbol_t *res_sym = check_symbol(GET_SYMBOL(obj)->str);
	if (res_sym != NULL && res_sym->value != NOVALUE)
            return res_sym->value;
	else
            error("Unknown SYMBOL: %s", GET_SYMBOL(obj)->str);
    }
}

object_t eval(object_t obj, object_t env)
{
    current_env = env;
    if (obj == NULLOBJ)
        return NULLOBJ;
    else if (TYPE(obj) == NUMBER || TYPE(obj) == BIGNUMBER || TYPE(obj) == STRING || TYPE(obj) == ARRAY)
	return obj;
    else if (TYPE(obj) == SYMBOL)
        return eval_symbol(obj);
    else if (TYPE(obj) == PAIR) {
	object_t first = FIRST(obj);
	if (TYPE(first) == PAIR) {
	    is_lambda(first);
	    return eval_func(first, eval_args(TAIL(obj), env), env);
	}
	symbol_t *s = find_symbol(GET_SYMBOL(first)->str);
	object_t args;
	if (is_special_form(s) || s->macro != NULLOBJ)
	    args = TAIL(obj);
	else
	    args = eval_args(TAIL(obj), env);
	if (s->lambda != NULLOBJ)
	    return eval_func(s->lambda, args, env);
	else if (s->func != NULL)
	    return s->func(args);
	else if (s->macro != NULLOBJ)
	    return macro_call(s->macro, args, env);
	else
	    error("Unknown func: %s", s->str);
    } else
        error("Unknown object_type");
    current_env = env;
}

void set_in_env(object_t env, object_t sym, object_t val)
{
    if (env == NULLOBJ)
	error("ERROR: NULLOBJ as env in set_in_env");
    object_t pair = FIRST(env);
    object_t var = FIRST(pair);
    if (GET_SYMBOL(var) == GET_SYMBOL(sym))
	TAIL(pair) = val;
    else
	set_in_env(TAIL(env), sym, val);
}

object_t setq_rec(object_t params)
{
    if (params == NULLOBJ)
	return NULLOBJ;
    symbol_t *sym = GET_SYMBOL(FIRST(params));
    object_t res;
    int find_res = find_in_env(current_env, FIRST(params), &res);
    if (!find_res)
	sym = find_symbol(GET_SYMBOL(FIRST(params))->str);
    if (TAIL(params) == NULLOBJ)
 	error("setq: no value");
    object_t obj = eval(SECOND(params), current_env);
    if (find_res)
	set_in_env(current_env, FIRST(params), obj);
    else
	sym->value = obj;
    if (TAIL(TAIL(params)) == NULLOBJ)
 	return obj;
    return setq_rec(TAIL(TAIL(params)));
}

object_t setq(object_t params)
{
    if (params == NULLOBJ)
 	error("setq: params = NULLOBJ");
    return setq_rec(params);
}

object_t and(object_t params)
{
    if (params == NULLOBJ)
	error("and: no params");
    while (params != NULLOBJ) {
	object_t first = FIRST(params);
	object_t res = eval(first, current_env);
	if (res == nil)
	    return nil;
	else if (res == t)
	    params = TAIL(params);
	else
	    error("and: invalid param");
    }
    return t;
}

object_t or(object_t params)
{
    if (params == NULLOBJ)
 	error("or: no params");
    while (params != NULLOBJ) {
 	object_t first = FIRST(params);
 	object_t res = eval(first, current_env);
 	if (res == t)
 	    return t;
 	else if (res == nil)
 	    params = TAIL(params);
 	else
 	    error("or: invalid param");
    }
    return nil;
}

object_t macroexpand(object_t params)
{
    if (params == NULLOBJ)
 	error("macroexpand: no params");
    if (TAIL(params) != NULLOBJ)
 	error("macroexpand: many params");
    object_t macro_c = FIRST(params);
    if (TYPE(macro_c) != PAIR)
 	error("macroexpand: invalid macro call");
    object_t macro_name = FIRST(macro_c);
    object_t macro;
    if (macro_name == NULLOBJ || TYPE(macro_name) != SYMBOL || GET_SYMBOL(macro_name)->macro == NULLOBJ)
 	error("macroexpand: invalid macro");
    macro = GET_SYMBOL(macro_name)->macro;
    object_t args = TAIL(macro_c);
    object_t new_env = make_env(SECOND(macro), args);
    append_env(new_env, current_env);
    object_t body = TAIL(TAIL(macro));
    object_t eval_res;
    object_t res = NULLOBJ;
    while (body != NULLOBJ) {
 	eval_res = eval(FIRST(body), new_env);
 	if (res == NULLOBJ)
 	    res = eval_res;
 	else if (TYPE(res) == STRING)
 	    res = NULLOBJ;
 	else
 	    append_env(res, eval_res);
 	body = TAIL(body);
    }
    return res;
}

object_t funcall(object_t params)
{
    if (params == NULLOBJ)
	error("funcall: no arguments");
    object_t func = FIRST(params);
    if (func == NULLOBJ || TYPE(func) != SYMBOL &&
	!(TYPE(func) == PAIR && is_lambda(func) == 1))
	error("funcall: invalid func");
    object_t args = TAIL(params);
    if (TYPE(func) == PAIR)
	return eval_func(func, args, current_env);
    symbol_t *s = find_symbol(GET_SYMBOL(func)->str);
    if (s->lambda != NULLOBJ)
	return eval_func(s->lambda, args, current_env);
    else if (s->func != NULL)
 	return s->func(args);
    else
 	error("Unknown func: %s", s->str);
}

object_t list(object_t args)
{
    return args;
}

object_t lisp_eval(object_t args)
{
    return eval(FIRST(args), current_env);
}

object_t error_func(object_t args)
{
    printf("ERROR: ");
    PRINT(FIRST(args));
    longjmp(repl_buf, 1);
}

object_t tagbody(object_t params)
{
    object_t obj;
    object_t form;
    while (params != NULLOBJ) {
        obj = FIRST(params);
        if (TYPE(obj) != SYMBOL)
            form = eval(obj, current_env);
	params = TAIL(params);
    }
    return form;
}

object_t block(object_t list)
{
    object_t obj;
    if (list == NULLOBJ)
	error("block: no arguments\n");
    if (setjmp(block_buf) == 0)
        return progn(list);
}

object_t return_from(object_t arg)
{
    return arg;
}

object_t labels(object_t param)
{
    return param;
}

void init_eval()
{
    register_func("ATOM", atom);
    register_func("EQ", eq);
    register_func("QUOTE", quote);
    register_func("BACKQUOTE",backquote);
    register_func("COND", cond);
    register_func("DEFUN", defun);
    register_func("DEFMACRO", defmacro);
    register_func("PROGN", progn);
    register_func("SETQ", setq);
    register_func("OR", or);
    register_func("AND", and);
    register_func("MACROEXPAND", macroexpand);
    register_func("FUNCALL", funcall);
    register_func("LIST", list);
    register_func("EVAL", lisp_eval);
    register_func("GC", print_gc_stat);
    register_func("ERROR", error_func);
    register_func("TAGBODY", tagbody);
    register_func("BLOCK", block);
    register_func("RETURN_FROM", return_from);
    register_func("BLOCK", block);
    register_func("LABELS", labels);
    t = NEW_SYMBOL("T");
    nil = NULLOBJ;
    quote_sym = find_symbol("QUOTE");
    backquote_sym = find_symbol("BACKQUOTE");
    lambda_sym = find_symbol("LAMBDA");
    cond_sym = find_symbol("COND");
    defun_sym = find_symbol("DEFUN");
    defmacro_sym = find_symbol("DEFMACRO");
    setq_sym = find_symbol("SETQ");
    or_sym = find_symbol("OR");
    and_sym = find_symbol("AND");
    t_sym = GET_SYMBOL(t);
    t_sym->value = t;
    nil_sym = find_symbol("NIL");
    nil_sym->value = nil;
    rest_sym = find_symbol("&REST");
    tagbody_sym = find_symbol("TAGBODY");
    block_sym = find_symbol("BLOCK");
    labels_sym = find_symbol("LABEL");
    progn_sym = find_symbol("PROGN");
}

