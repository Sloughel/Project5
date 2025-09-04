#include"stu.h"
void test_for_clauses_set(solver* s, int clauses_number);
void show_pos_pos_clauses(solver* s, int variables_number);
FILE* open_input_file_pointer(const char* filename);
bool get_result(solver* s);
bool output_the_res(const char* filename, int variables_number, solver* s);
bool test(const char* filename);


int main() {
	if(!test("sat-20.cnf"))return ERROR;
	/*if (!test("2.cnf"))return ERROR;
	if (!test("3.cnf"))return ERROR;
	if (!test("4（unsatisfied）.cnf"))return ERROR;
	if (!test("5.cnf"))return ERROR;
	if (!test("6.cnf"))return ERROR;*/
	return 0;
}

bool test(const char* filename) {
	FILE* input = NULL;
	solver* s = NULL;
	int variables_number = 0, clauses_number = 0;

	input = open_input_file_pointer(filename);//open the input file
	if (input == NULL)goto error;

	if (!read_variables_and_clauses_num(input, &variables_number, &clauses_number))goto error;//read in var_count and clauses_count
	////////////////////

	if ((s = init_solver(input, variables_number, clauses_number)) == NULL)goto error;//init solver

	//test_for_clauses_set(s, clauses_number);//test for clauses set reading
	//show_pos_pos_clauses(s, variables_number);//test for pos_clauses and neg_clauses

	fclose(input); input = NULL;//close the input file pointer

	printf("filename is %s\n", filename);//the solver has been ready

	if (get_result(s))              //the dpll
		if (!output_the_res(filename, variables_number, s))goto error;//output

	////////////////////

	free_solver(s, clauses_number, variables_number); ///free
	return true;

error:
	if (input != NULL)fclose(input);
	if (s != NULL)free_solver(s, clauses_number, variables_number);
	return false;
}

bool output_the_res(const char* filename, int variables_number, solver* s) {
	FILE* out;
	char fullpath[256];
	snprintf(fullpath, sizeof(fullpath), "%s/%s.res", "output", filename);
	errno_t err = fopen_s(&out, fullpath, "w");
	if (err != 0)return false;
	for (int i = 0; i < variables_number; i++) {
		Assignment assign = s->variables[i].assignment;
		if (assign == TRUE)fprintf(out, "%d ", i + 1);
		else if (assign == FALSE)fprintf(out, "%d ", -(i + 1));
		else if (assign == UNSIGNNED)fprintf(out, "0 ");
	}
	fclose(out);
	return true;
}


FILE* open_input_file_pointer(const char* filename) {
	FILE* input;
	char fullpath[512];
	snprintf(fullpath, sizeof(fullpath), "%s/%s", "input", filename);
	errno_t err = fopen_s(&input, fullpath, "r");
	if (err != 0) {
		printf("fail to open the file %s\n", filename);
		return NULL;
	}
	return input;
}
bool get_result(solver* s) {
	bool result = false;
	clock_t start = clock();
	result = dpll(s);
	clock_t end = clock();

	printf("clauses %s\n", result == true ? "satisfied" : "unsatisfied");
	printf("executation time:%4fms\n", ((double)(end - start) / CLOCKS_PER_SEC)*1000);
	return result;
}




void test_for_clauses_set(solver* s, int clauses_number) {
	for (int i = 0; i < clauses_number; i++) {
		int value, sign;
		for (unsigned int j = 0; j < s->clauses[i].size; j++) {
			value = s->clauses[i].literals[j].value;
			sign = s->clauses[i].literals[j].sign;
			if (sign == false)putchar('-');
			printf("%d ", value);
		}
		printf("\n");
	}
}

void show_pos_pos_clauses(solver* s, int variables_number) {
	for (int i = 0; i < variables_number; i++) {
		Variable var = s->variables[i];
		printf("变量%d的negtive子句如下：\n", i + 1);
		for (int j = 0; j < var.neg_count; j++) {
			for (unsigned int k = 0; k < var.neg_clauses[j]->size; k++) {
				if (var.neg_clauses[j]->literals[k].sign == false)putchar('-');
				printf("%d ", var.neg_clauses[j]->literals[k].value);
			}
			printf("\n");
		}
		printf("变量%d的postive子句如下:\n", i + 1);
		for (int j = 0; j < var.pos_count; j++) {
			for (unsigned int k = 0; k < var.pos_clauses[j]->size; k++) {
				if (var.pos_clauses[j]->literals[k].sign == false)putchar('-');
				printf("%d ", var.pos_clauses[j]->literals[k].value);
			}
			printf("\n");
		}
	}
}