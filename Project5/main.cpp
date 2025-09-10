#include"stu.h"

bool test(const char* filename);
bool output_the_res(const char* filename, int variables_number, solver* s, bool result, double executation_time);
FILE* open_input_file_pointer(const char* filename);
bool get_result(solver* s, double* executation_time);
void show_pos_pos_clauses(solver* s, int variables_number);
void test_for_clauses_set(solver* s, int clauses_number);


clock_t ST;
bool is_over_time = false;

int main() {
	const char file[12][100] = { "1.cnf", "2.cnf","3.cnf","4（unsatisfied）.cnf","5.cnf","6.cnf","7（unsatisfied）.cnf","8（unsatisfied）.cnf",
	"9（unsatisfied）.cnf","10.cnf","11（unsatisfied）.cnf","12.cnf"};
	for(int i=0;i<12;i++)
	if (!test(file[i]))return ERROR;
	
	

	//if (!sudoku_test())return ERROR;
	return 0;
}

/// <summary>
/// 这是用于测试cnf经典文件的函数，从input文件夹内的cnf文件输入
/// </summary>
/// <param name="filename">cnf文件的文件名</param>
/// <returns>是否成功完成测试</returns>

bool test(const char* filename) {
	FILE* input = NULL;
	solver* s = NULL;
	double executation_time = 0;
	bool result = false;
	int variables_number = 0, clauses_number = 0;

	input = open_input_file_pointer(filename);//open the input file
	if (input == NULL)goto error;

	if (!read_variables_and_clauses_num(input, &variables_number, &clauses_number))goto error;//read in var_count and clauses_count

	if ((s = init_solver(input, variables_number, clauses_number)) == NULL)goto error;//init solver

	//test_for_clauses_set(s, clauses_number);//test for clauses set reading
	//show_pos_pos_clauses(s, variables_number);//test for pos_clauses and neg_clauses

	fclose(input); input = NULL;//close the input file pointer

	printf("filename is %s\n", filename);//the solver has been ready

	result = get_result(s, &executation_time);           //the dpll

	if (!output_the_res(filename, variables_number, s,result,executation_time))goto error;//output

	free_solver(s, clauses_number, variables_number); ///free
	return true;

error:
	if (input != NULL)fclose(input);
	if (s != NULL)free_solver(s, clauses_number, variables_number);
	return false;
}
/// <summary>
/// 这是用于将SAT问题答案输出的函数
/// </summary>
/// <param name="filename">cnf问题的文件名</param>
/// <param name="variables_number">变量数，用以确定输出的答案的数量</param>
/// <param name="s">s为求解器，从求解器的状态来确定答案</param>
/// <param name="result">根据答案的正确与否来确定输出的状态</param>
/// <param name="executation_time">处理问题所用的时间</param>
/// <returns>是否完成输出</returns>
bool output_the_res(const char* filename, int variables_number, solver* s,bool result,double executation_time) {
	FILE* out;
	char fullpath[256];
	snprintf(fullpath, sizeof(fullpath), "%s/%s.res", "output", filename);//确保输出文件在output文件夹下，并添加.res后缀

	errno_t err = fopen_s(&out, fullpath, "w");
	if (err != 0)return false;//open the file

	if (is_over_time)fprintf(out, "s -1\n");
	else {
		fprintf(out, "s %d\n", result ? 1 : 0);
		fprintf(out, "v ");
		for (int i = 0; i < variables_number; i++) {
			Assignment assign = s->variables[i].assignment;
			if (assign == TRUE)fprintf(out, "%d ", i + 1);
			else if (assign == FALSE)fprintf(out, "%d ", -(i + 1));
			else if (assign == UNSIGNNED)fprintf(out, "0 ");
		}
		fputc('\n', out);
		fprintf(out, "t %f", executation_time);
	}

	fclose(out);
	return true;
}

/// <summary>
/// 打开cnf问题的文件
/// </summary>
/// <param name="filename">cnf问题的文件名称</param>
/// <returns>已经打开相关文件的文件指针</returns>
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

/// <summary>
/// 调用dpll，确认结果的函数
/// </summary>
/// <param name="s">s为求解器，用来求解SAT问题</param>
/// <param name="execatation_time">用来存储处理所用的时间</param>
/// <returns>问题是否解出</returns>
bool get_result(solver* s,double *execatation_time) {
	bool result = false;
	clock_t start =ST=clock();//init the variables 
	
	result = dpll(s);// apply dpll

	clock_t end = clock();

	if (is_over_time)printf("over time\n");
	else {
		printf("clauses %s\n", result == true ? "satisfied" : "unsatisfied");
		*execatation_time = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
		printf("executation time:%.1fms\n", *execatation_time);
		printf("\n");
	}

	return result;
}


/// <summary>
/// 用来测试子句集是否正确读取的函数
/// </summary>
/// <param name="s">s为求解器，里面存储了子句集</param>
/// <param name="clauses_number">子句的数量</param>

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
/// <summary>
/// 用来测试Variabls类型下对积极和消极监视子句的存放情况
/// </summary>
/// <param name="s">s为求解器，其中存放了各个变量对其积极和消极的监视子句的存放情况</param>
/// <param name="variables_number">变量的数量</param>
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