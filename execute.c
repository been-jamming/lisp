#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "allocate.h"
#include "dictionary.h"

int global_none;
static char *error_message = "none";

void set_error(char *err){
	error_message = err;
}

int is_whitespace(char c){
	return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

void skip_whitespace(char **c){
	while(is_whitespace(**c)){
		++*c;
	}
}

int is_digit(char c){
	return c >= '0' && c <= '9';
}

int is_identifier_char(char c){
	return c && !is_whitespace(c) && c != '(' && c != ')' && c != '{' && c != '}';
}

int get_integer(char **c){
	int output = 0;

	if(**c == '-'){
		++*c;
		return -get_integer(c);
	}

	while(is_digit(**c)){
		output *= 10;
		output += **c - '0';
		++*c;
	}

	skip_whitespace(c);

	return output;
}

char *get_identifier_name(char **c){
	char *beginning;
	char *output;

	beginning = *c;
	while(is_identifier_char(**c)){
		++*c;
	}

	output = malloc(sizeof(char)*(*c - beginning + 1));
	if(!output){
		set_error("malloc returned NULL");
		return NULL;
	}

	memcpy(output, beginning, sizeof(char)*(*c - beginning));
	output[*c - beginning] = '\0';
	skip_whitespace(c);

	return output;
}

int get_quoted_identifier(char **c){
	char *name;
	int output;

	name = get_identifier_name(c);
	if(!name){
		return -1;
	}
	output = allocate();
	if(output == -1){
		return -1;
	}
	data_heap[output].type = IDENTIFIER;
	data_heap[output].identifier_name = name;

	return output;
}

int get_integer_data(char **c){
	int output;
	int int_value;

	int_value = get_integer(c);
	output = allocate();
	if(output == -1){
		return -1;
	}
	data_heap[output].type = INT_DATA;
	data_heap[output].int_value = int_value;

	return output;
}

int get_quoted_value(char **c);

int get_quoted_expression(char **c, data_type type){
	char end_char;
	int output;
	int value;
	int i;
	int *next_entries;

	if(type == S_EXPR){
		end_char = ')';
	} else {
		end_char = '}';
	}

	output = allocate();
	if(output == -1){
		return -1;
	}
	if(!push_shadow_stack(output)){
		return -1;
	}
	data_heap[output].num_entries = 0;
	data_heap[output].entries = NULL;

	skip_whitespace(c);
	while(**c != end_char){
		value = get_quoted_value(c);
		if(value == -1){
			return -1;
		}
		push_shadow_stack(value);
		data_heap[output].num_entries++;
		next_entries = realloc(data_heap[output].entries, sizeof(int)*data_heap[output].num_entries);
		if(!next_entries){
			return -1;
		}
		data_heap[output].entries = next_entries;
		data_heap[output].entries[data_heap[output].num_entries - 1] = value;
		skip_whitespace(c);
	}

	++*c;
	skip_whitespace(c);

	for(i = 0; i <= data_heap[output].num_entries; i++){
		pop_shadow_stack();
	}
	data_heap[output].type = type;

	return output;
}

int get_quoted_value(char **c){
	skip_whitespace(c);
	if(is_digit(**c) || (**c == '-' && is_digit((*c)[1]))){
		return get_integer_data(c);
	} else if(is_identifier_char(**c)){
		return get_quoted_identifier(c);
	} else if(**c == '('){
		++*c;
		return get_quoted_expression(c, S_EXPR);
	} else if(**c == '{'){
		++*c;
		return get_quoted_expression(c, Q_EXPR);
	} else {
		set_error("unrecognized expression value");
		return -1;
	}
}

void print_value(int value){
	int i;

	switch(data_heap[value].type){
		case INT_DATA:
			printf("%d", data_heap[value].int_value);
			return;
		case IDENTIFIER:
			printf("%s", data_heap[value].identifier_name);
			return;
		case S_EXPR:
			printf("(");
			for(i = 0; i < data_heap[value].num_entries; i++){
				print_value(data_heap[value].entries[i]);
				if(i < data_heap[value].num_entries - 1){
					printf(" ");
				}
			}
			printf(")");
			return;
		case Q_EXPR:
			printf("{");
			for(i = 0; i < data_heap[value].num_entries; i++){
				print_value(data_heap[value].entries[i]);
				if(i < data_heap[value].num_entries - 1){
					printf(" ");
				}
			}
			printf("}");
			return;
		case NONE_DATA:
			printf("none");
			return;
		case BUILTIN_FUNCTION:
			printf("[builtin_function]");
			return;
		case FUNCTION:
			printf("[function](");
			print_value(data_heap[value].var_list);
			printf(" ");
			print_value(data_heap[value].source);
			printf(")");
			return;
	}
}

int set_variable(char *var_name, int data_index){
	variable *var;

	var = read_dictionary(current_scope->variables, var_name, 0);
	if(!var){
		var = malloc(sizeof(variable));
		if(!var){
			set_error("malloc returned NULL");
			return 0;
		}
		var->name = malloc(sizeof(char)*(strlen(var_name) + 1));
		if(!var->name){
			free(var);
			set_error("malloc returned NULL");
			return 0;
		}
		var->data_index = data_index;
		data_heap[data_index].num_references++;
		write_dictionary(&(current_scope->variables), var_name, var, 0);
		return 1;
	} else {
		decrement_references(var->data_index);
		var->data_index = data_index;
		data_heap[data_index].num_references++;
		return 1;
	}
}

int evaluate_q_expression(int data_index, int expand_q_expr);

int execute_s_expr(int data_index){
	int next_data_index;
	int identifier_value;
	int function;
	int i;
	int made_scope = 0;
	int tail_call;

	data_heap[data_index].num_references++;
	do{
		if(!push_shadow_stack(data_index)){
			return -1;
		}
		tail_call = 0;
		if(data_heap[data_index].num_entries == 0){
			set_error("empty function call");
			return -1;
		}
		function = evaluate_q_expression(data_heap[data_index].entries[0], 0);
		if(function == -1){
			return -1;
		}
		while(data_heap[function].type == FUNCTION){
			if(!made_scope){
				if(!next_scope()){
					return -1;
				}
				made_scope = 1;
			}
			if(data_heap[data_heap[function].var_list].type != Q_EXPR){
				set_error("expected a Q expression for function variable list");
				return -1;
			}
			if(data_heap[data_heap[function].var_list].num_entries != data_heap[data_index].num_entries - 1){
				set_error("function called with wrong number of arguments");
				return -1;
			}
			for(i = 0; i < data_heap[data_heap[function].var_list].num_entries; i++){
				if(data_heap[data_heap[data_heap[function].var_list].entries[i]].type != IDENTIFIER){
					set_error("expected identifier name in function variable list");
					return -1;
				}
				identifier_value = evaluate_q_expression(data_heap[data_index].entries[i + 1], 0);
				if(identifier_value == -1){
					return -1;
				}
				if(!set_variable(data_heap[data_heap[data_heap[function].var_list].entries[i]].identifier_name, identifier_value)){
					return -1;
				}
				decrement_references(identifier_value);
			}
			next_data_index = data_heap[function].source;
			if(data_heap[next_data_index].type != Q_EXPR){
				set_error("expected a Q expression for function source");
				return -1;
			}
			if(data_heap[next_data_index].num_entries == 0){
				set_error("empty function call");
				return -1;
			}
			data_heap[next_data_index].num_references++;
			pop_shadow_stack();
			if(!push_shadow_stack(next_data_index)){
				return -1;
			}
			decrement_references(data_index);
			decrement_references(function);
			data_index = next_data_index;
			function = evaluate_q_expression(data_heap[data_index].entries[0], 0);
		}
		if(data_heap[function].type != BUILTIN_FUNCTION){
			set_error("expected function or builtin_function for function call");
			return -1;
		}
		next_data_index = data_heap[function].builtin_function(data_index, &tail_call);
		if(next_data_index == -1){
			return -1;
		}
		decrement_references(pop_shadow_stack());
		decrement_references(function);
		data_index = next_data_index;
	} while(tail_call);

	if(made_scope){
		previous_scope();
	}

	return data_index;
}

int evaluate_q_expression(int data_index, int expand_q_expr){
	int output;
	int i;
	scope *search_scope;
	variable *var;

	switch(data_heap[data_index].type){
		case INT_DATA:
			output = allocate();
			if(output == -1){
				return -1;
			}
			data_heap[output].type = INT_DATA;
			data_heap[output].int_value = data_heap[data_index].int_value;
			return output;
		case IDENTIFIER:
			search_scope = current_scope;
			while(search_scope){
				var = read_dictionary(search_scope->variables, data_heap[data_index].identifier_name, 0);
				if(var){
					output = var->data_index;
					data_heap[output].num_references++;
					return output;
				}
				search_scope = search_scope->previous;
			}
			set_error("unrecognized variable");
			return -1;
		case Q_EXPR:
		case S_EXPR:
			if(data_heap[data_index].type == S_EXPR || expand_q_expr){
				return execute_s_expr(data_index);
			} else {
				data_heap[data_index].num_references++;
				return data_index;
			}
		case BUILTIN_FUNCTION:
		case FUNCTION:
		case NONE_DATA:
			data_heap[data_index].num_references++;
			return data_index;
	}

	set_error("unrecognized expression type");
	return -1;
}

int data_equal(int b, int a){
	int i;

	if(data_heap[a].type != data_heap[b].type){
		return 0;
	}

	switch(data_heap[a].type){
		case NONE_DATA:
			return 1;
		case INT_DATA:
			return data_heap[a].int_value == data_heap[b].int_value;
		case IDENTIFIER:
			return !strcmp(data_heap[a].identifier_name, data_heap[b].identifier_name);
		case S_EXPR:
		case Q_EXPR:
			if(data_heap[a].num_entries != data_heap[b].num_entries){
				return 0;
			}
			for(i = 0; i < data_heap[a].num_entries; i++){
				if(!data_equal(data_heap[a].entries[i], data_heap[b].entries[i])){
					return 0;
				}
			}
			return 1;
		case BUILTIN_FUNCTION:
			return data_heap[a].builtin_function == data_heap[b].builtin_function;
		case FUNCTION:
			return data_equal(data_heap[a].var_list, data_heap[b].var_list) && data_equal(data_heap[a].source, data_heap[b].source);
	}

	return 0;
}

int register_builtin_function(char *name, int (*builtin_function)(int, int *)){
	int data_index;
	variable *var;

	data_index = allocate();
	if(data_index == -1){
		return -1;
	}
	data_heap[data_index].type = BUILTIN_FUNCTION;
	data_heap[data_index].builtin_function = builtin_function;
	var = malloc(sizeof(variable));
	if(!var){
		set_error("malloc returned NULL");
		decrement_references(data_index);
		return -1;
	}
	var->name = malloc(sizeof(char)*(strlen(name) + 1));
	if(!var->name){
		set_error("malloc returned NULL");
		free(var);
		decrement_references(data_index);
		return -1;
	}
	strcpy(var->name, name);
	var->data_index = data_index;

	write_dictionary(&(global_scope->variables), name, var, 0);
	return data_index;
}

int print(int expr, int *tail_call){
	int i;
	int arg_value;

	for(i = 1; i < data_heap[expr].num_entries; i++){
		if(i - 1){
			printf(" ");
		}
		arg_value = evaluate_q_expression(data_heap[expr].entries[i], 0);
		if(arg_value == -1){
			return -1;
		}
		print_value(arg_value);
		decrement_references(arg_value);
	}

	printf("\n");
	data_heap[global_none].num_references++;
	return global_none;
}

int add(int expr, int *tail_call){
	int output = 0;
	int output_index;
	int arg_value;
	int i;

	for(i = 1; i < data_heap[expr].num_entries; i++){
		arg_value = evaluate_q_expression(data_heap[expr].entries[i], 0);
		if(arg_value == -1){
			return -1;
		}
		if(data_heap[arg_value].type != INT_DATA){
			set_error("expected integer value");
			return -1;
		}
		output += data_heap[arg_value].int_value;
		decrement_references(arg_value);
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int subtract(int expr, int *tail_call){
	int output;
	int output_index;
	int arg_value;
	int i;

	if(data_heap[expr].num_entries < 2){
		set_error("- expects at least one argument");
		return -1;
	}

	arg_value = evaluate_q_expression(data_heap[expr].entries[1], 0);
	if(arg_value == -1){
		return -1;
	}
	if(data_heap[arg_value].type != INT_DATA){
		set_error("expected integer value");
		return -1;
	}
	if(data_heap[expr].num_entries == 2){
		output = -data_heap[arg_value].int_value;
		decrement_references(arg_value);
		output_index = allocate();
		if(output_index == -1){
			return -1;
		}
		data_heap[output_index].type = INT_DATA;
		data_heap[output_index].int_value = output;

		return output_index;
	} else {
		output = data_heap[arg_value].int_value;
		decrement_references(arg_value);
		for(i = 2; i < data_heap[expr].num_entries; i++){
			arg_value = evaluate_q_expression(data_heap[expr].entries[i], 0);
			if(arg_value == -1){
				return -1;
			}
			if(data_heap[arg_value].type != INT_DATA){
				set_error("expected integer value");
				return -1;
			}
			output -= data_heap[arg_value].int_value;
			decrement_references(arg_value);
		}
		output_index = allocate();
		if(output_index == -1){
			return -1;
		}
		data_heap[output_index].type = INT_DATA;
		data_heap[output_index].int_value = output;

		return output_index;
	}
}

int multiply(int expr, int *tail_call){
	int output = 1;
	int output_index;
	int arg_value;
	int i;

	for(i = 1; i < data_heap[expr].num_entries; i++){
		arg_value = evaluate_q_expression(data_heap[expr].entries[i], 0);
		if(arg_value == -1){
			return -1;
		}
		if(data_heap[arg_value].type != INT_DATA){
			set_error("expected integer value");
			return -1;
		}
		output *= data_heap[arg_value].int_value;
		decrement_references(arg_value);
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int if_func(int expr, int *tail_call){
	int arg_value;

	if(data_heap[expr].num_entries == 3){
		arg_value = evaluate_q_expression(data_heap[expr].entries[1], 0);
		if(arg_value == -1){
			return -1;
		}
		if(data_heap[arg_value].type != INT_DATA || data_heap[arg_value].int_value){
			decrement_references(arg_value);
			if(data_heap[data_heap[expr].entries[2]].type == S_EXPR){
				*tail_call = 1;
				data_heap[data_heap[expr].entries[2]].num_references++;
				return data_heap[expr].entries[2];
			} else {
				return evaluate_q_expression(data_heap[expr].entries[2], 0);
			}
		} else {
			decrement_references(arg_value);
			data_heap[global_none].num_references++;
			return global_none;
		}
	} else if(data_heap[expr].num_entries == 4){
		arg_value = evaluate_q_expression(data_heap[expr].entries[1], 0);
		if(arg_value == -1){
			return -1;
		}
		if(data_heap[arg_value].type != INT_DATA || data_heap[arg_value].int_value){
			decrement_references(arg_value);
			if(data_heap[data_heap[expr].entries[2]].type == S_EXPR){
				*tail_call = 1;
				data_heap[data_heap[expr].entries[2]].num_references++;
				return data_heap[expr].entries[2];
			} else {
				return evaluate_q_expression(data_heap[expr].entries[2], 0);
			}
		} else {
			decrement_references(arg_value);
			if(data_heap[data_heap[expr].entries[3]].type == S_EXPR){
				*tail_call = 1;
				data_heap[data_heap[expr].entries[3]].num_references++;
				return data_heap[expr].entries[3];
			} else {
				return evaluate_q_expression(data_heap[expr].entries[3], 0);
			}
		}
	} else {
		set_error("if expects 2 or 3 arguments");
		return -1;
	}
}

int equal(int expr, int *tail_call){
	int output = 1;
	int output_index;
	int first;
	int arg_value;
	int i;

	if(data_heap[expr].num_entries < 2){
		set_error("= expects at least 1 argument");
		return -1;
	}

	first = evaluate_q_expression(data_heap[expr].entries[1], 0);
	if(first == -1){
		return -1;
	}
	push_shadow_stack(first);

	for(i = 2; i < data_heap[expr].num_entries; i++){
		arg_value = evaluate_q_expression(data_heap[expr].entries[i], 0);
		if(arg_value == -1){
			return -1;
		}
		if(!data_equal(arg_value, first)){
			output = 0;
			decrement_references(arg_value);
			break;
		}
		decrement_references(arg_value);
	}

	decrement_references(pop_shadow_stack());
	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int set(int expr, int *tail_call){
	int set_value;

	if(data_heap[expr].num_entries != 3){
		set_error("set expects 2 arguments");
		return -1;
	}

	if(data_heap[data_heap[expr].entries[1]].type != IDENTIFIER){
		set_error("set expectes identifier as first argument");
		return -1;
	}

	set_value = evaluate_q_expression(data_heap[expr].entries[2], 0);
	if(set_value == -1){
		return -1;
	}
	if(!set_variable(data_heap[data_heap[expr].entries[1]].identifier_name, set_value)){
		return -1;
	}
	decrement_references(set_value);

	data_heap[global_none].num_references++;
	return global_none;
}

int lambda(int expr, int *tail_call){
	int output_index;
	int var_list;
	int source;

	if(data_heap[expr].num_entries != 3){
		set_error("lambda expects 2 arguments");
		return -1;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	var_list = evaluate_q_expression(data_heap[expr].entries[1], 0);
	if(var_list == -1){
		return -1;
	}
	push_shadow_stack(var_list);
	source = evaluate_q_expression(data_heap[expr].entries[2], 0);
	if(source == -1){
		return -1;
	}
	pop_shadow_stack(var_list);
	data_heap[output_index].type = FUNCTION;
	data_heap[output_index].var_list = var_list;
	data_heap[output_index].source = source;

	return output_index;
}

int colon(int expr, int *tail_call){
	int arg_value;
	int num_entries;
	int i;

	num_entries = data_heap[expr].num_entries;
	if(num_entries < 2){
		data_heap[global_none].num_references++;
		return global_none;
	}

	for(i = 1; i < num_entries - 1; i++){
		arg_value = evaluate_q_expression(data_heap[expr].entries[i], 0);
		if(arg_value == -1){
			return -1;
		}
		decrement_references(arg_value);
	}

	if(data_heap[data_heap[expr].entries[num_entries - 1]].type == S_EXPR){
		*tail_call = 1;
		data_heap[data_heap[expr].entries[num_entries - 1]].num_references++;
		return data_heap[expr].entries[num_entries - 1];
	} else {
		return evaluate_q_expression(data_heap[expr].entries[num_entries - 1], 0);
	}
}

int eval(int expr, int *tail_call){
	int arg_value;
	int output_index;

	if(data_heap[expr].num_entries != 2){
		set_error("eval expects exactly one argument");
		return -1;
	}

	arg_value = evaluate_q_expression(data_heap[expr].entries[1], 0);
	if(arg_value == -1){
		return -1;
	}
	if(data_heap[arg_value].type != Q_EXPR){
		set_error("eval expects a Q expression as its first argument");
		return -1;
	}
	output_index = evaluate_q_expression(arg_value, 1);
	if(output_index == -1){
		return -1;
	}
	decrement_references(arg_value);
	return output_index;
}

int main(int argc, char **argv){
	char input[1024];
	char *input_pointer;
	int data;
	int result;

	if(!initialize_heap(10000)){
		fprintf(stderr, "Error: failed to initialize heap\n");
		return 1;
	}
	if(!create_global_scope()){
		fprintf(stderr, "Error: failed to create global scope\n");
		return 1;
	}
	data = allocate();
	if(data == -1){
		fprintf(stderr, "Error: %s\n", error_message);
		return 1;
	}
	data_heap[data].type = NONE_DATA;
	push_shadow_stack(data);
	global_none = data;
	register_builtin_function("print", print);
	register_builtin_function("+", add);
	register_builtin_function("-", subtract);
	register_builtin_function("*", multiply);
	register_builtin_function("if", if_func);
	register_builtin_function("=", equal);
	register_builtin_function("set", set);
	register_builtin_function("lambda", lambda);
	register_builtin_function(":", colon);
	register_builtin_function("eval", eval);

	while(1){
		printf("lisp> ");
		fgets(input, 256, stdin);
		input_pointer = input;
		data = get_quoted_value(&input_pointer);
		push_shadow_stack(data);
		if(data == -1){
			fprintf(stderr, "Error: %s\n", error_message);
			clear_shadow_stack();
			push_shadow_stack(global_none);
			continue;
		}
		result = evaluate_q_expression(data, 0);
		if(result == -1){
			fprintf(stderr, "Error: %s\n", error_message);
			clear_shadow_stack();
			push_shadow_stack(global_none);
			decrement_references(data);
			continue;
		}

		if(data_heap[result].type != NONE_DATA){
			print_value(result);
			printf("\n");
		}
		pop_shadow_stack();
		decrement_references(data);
		decrement_references(result);
		printf("num_allocated: %d\n", num_allocated);
	}
}

