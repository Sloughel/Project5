#pragma once
#include<stdlib.h>
#include<stdio.h>
#include<time.h>
#include<string.h>
#include<stdbool.h>
extern clock_t NOW, ST;
extern bool is_over_time;

#define ERROR -1
#define SIZE 9
#define EMPTY 0
typedef enum {
	TRUE,
	FALSE,
	UNSIGNNED
}Assignment;

typedef struct {
	int value;
	bool sign;
}Literals;
typedef struct {
	Literals*literals;
	unsigned int size;
	int watch1, watch2;
	bool is_learned;
}Clause;
typedef struct {
	Assignment assignment;
	double activity;
	int neg_count, pos_count;
	int decision_level;
	Clause** pos_clauses, ** neg_clauses;
	Clause* reason;
}Variable;
typedef struct {
	Clause* clauses;
	Variable* variables;
	int decision_level;
	int var_count,clause_count;
	int* trail;
	int* trail_level;
	int trail_size;
	int assigned_num;
	double var_increasement;
	int clause_max_size;
}solver;

bool read_variables_and_clauses_num(FILE* fp, int* variable_number, int* clause_number);
Literals* get_clauses_set(FILE* fp, int* size,int variables_number);
solver* init_solver(FILE*input,int variables_number, int clause_number);
bool add(solver* s, FILE* input, int clauses_number, int variables_number);
bool add_clauses(solver* s, Literals* literals, int clauses_idx, int size, int variables_number);
void free_solver(solver* s, int clauses_number, int variables_number);
bool dpll(solver* s);
int get_num_from_file(FILE* fp);
bool sudoku_test();