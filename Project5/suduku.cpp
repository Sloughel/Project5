#include"stu.h"

void printSudoku(int sudoku[SIZE][SIZE]) {
    printf("--------------------\n");
    for (int i = 0; i < SIZE; i++) {
        if (i % 3 == 0 && i != 0) {
            printf("------+-------+------\n");
        }
        for (int j = 0; j < SIZE; j++) {
            if (j % 3 == 0 && j != 0) {
                printf("| ");
            }
            if (sudoku[i][j] == EMPTY) {
                printf("  ");
            }
            else {
                printf("%d ", sudoku[i][j]);
            }
        }
        printf("\n");
    }
    printf("--------------------\n");

}
bool isRowValid(int sudoku[SIZE][SIZE], int row, int num) {
    for (int col = 0; col < SIZE; col++) {
        if (sudoku[row][col] == num) {
            return false;
        }
    }
    return true;
}
bool isColValid(int sudoku[SIZE][SIZE], int col, int num) {
    for (int row = 0; row < SIZE; row++) {
        if (sudoku[row][col] == num) {
            return false;
        }
    }
    return true;
}
bool isBoxValid(int sudoku[SIZE][SIZE], int startRow, int startCol, int num) {
    for (int row = 0; row < 3; row++) {
        for (int col = 0; col < 3; col++) {
            if (sudoku[startRow + row][startCol + col] == num) {
                return false;
            }
        }
    }
    return true;
}

// 检查数字在当前位置是否合法
bool isValid(int sudoku[SIZE][SIZE], int row, int col, int num) {
    return isRowValid(sudoku, row, num) &&
        isColValid(sudoku, col, num) &&
        isBoxValid(sudoku, row - row % 3, col - col % 3, num);
}

// 寻找下一个空白位置
bool findEmptyLocation(int sudoku[SIZE][SIZE], int* row, int* col) {
    for (*row = 0; *row < SIZE; (*row)++) {
        for (*col = 0; *col < SIZE; (*col)++) {
            if (sudoku[*row][*col] == EMPTY) {
                return true;
            }
        }
    }
    return false;
}

// 求解数独并统计解的数量
int solveSudokuCount(int sudoku[SIZE][SIZE], int maxSolutions) {
    int row, col;

    // 如果没有空白位置，找到一个解
    if (!findEmptyLocation(sudoku, &row, &col)) {
        return 1;
    }

    int solutions = 0;

    // 尝试填入1-9
    for (int num = 1; num <= SIZE; num++) {
        if (isValid(sudoku, row, col, num)) {
            sudoku[row][col] = num;

            // 递归求解
            solutions += solveSudokuCount(sudoku, maxSolutions - solutions);

            // 如果解的数量超过maxSolutions，提前返回
            if (solutions >= maxSolutions) {
                sudoku[row][col] = EMPTY; // 回溯
                return solutions;
            }

            sudoku[row][col] = EMPTY; // 回溯
        }
    }

    return solutions;
}

// 生成完整的数独终盘
bool generateFullSudoku(int sudoku[SIZE][SIZE]) {
    int row, col;

    // 如果没有空白位置，数独完成
    if (!findEmptyLocation(sudoku, &row, &col)) {
        return true;
    }

    // 随机排列1-9，增加随机性
    int nums[SIZE] = { 1, 2, 3, 4, 5, 6, 7, 8, 9 };
    for (int i = SIZE - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        int temp = nums[i];
        nums[i] = nums[j];
        nums[j] = temp;
    }

    // 尝试填入数字
    for (int i = 0; i < SIZE; i++) {
        int num = nums[i];
        if (isValid(sudoku, row, col, num)) {
            sudoku[row][col] = num;

            // 递归生成
            if (generateFullSudoku(sudoku)) {
                return true;
            }

            sudoku[row][col] = EMPTY; // 回溯
        }
    }

    return false; // 用于回溯
}

// 复制数独
void copySudoku(int dest[SIZE][SIZE], int src[SIZE][SIZE]) {
    for (int i = 0; i < SIZE; i++) {
        for (int j = 0; j < SIZE; j++) {
            dest[i][j] = src[i][j];
        }
    }
}

// 挖洞法生成数独谜题
void generateSudokuPuzzle(int puzzle[SIZE][SIZE], int difficulty) {
    // 初始化数独为空
    for (int i = 0; i < SIZE; i++) {
        for (int j = 0; j < SIZE; j++) {
            puzzle[i][j] = EMPTY;
        }
    }

    // 生成完整数独
    generateFullSudoku(puzzle);

    // 根据难度确定挖洞数量（难度越高，挖洞越多）
    int holes;
    switch (difficulty) {
    case 1: holes = 30; break; // 简单
    case 2: holes = 40; break; // 中等
    case 3: holes = 50; break; // 困难
    default: holes = 35; // 默认
    }

    // 复制一份用于挖洞测试
    int temp[SIZE][SIZE];
    copySudoku(temp, puzzle);

    int count = 0;
    // 随机挖洞，确保至少有一个解且解唯一
    while (count < holes) {
        int row = rand() % SIZE;
        int col = rand() % SIZE;

        // 如果已经是空格，跳过
        if (temp[row][col] == EMPTY) {
            continue;
        }

        // 保存当前值，用于恢复
        int value = temp[row][col];
        temp[row][col] = EMPTY;

        // 检查解的数量，最多检查2个解
        int solutions = solveSudokuCount(temp, 2);

        // 如果解唯一，保留这个洞
        if (solutions == 1) {
            puzzle[row][col] = EMPTY;
            count++;
        }
        else {
            // 否则恢复该值
            temp[row][col] = value;
        }
    }
}

int  sudoku_to_cnf(int sudoku[SIZE][SIZE],FILE*fp) {
    int size = 0;
    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k <= SIZE; k++) {
                fprintf(fp, "%d%d%d ", i, j, k);
            }
            fprintf(fp, "0"); size += 1;
            fprintf(fp,"\n");
        }
       fprintf(fp,"\n");
    }
    //表示每一个位置都可以填一到九这九个数字
    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k < SIZE; k++) {
                for (int m = k + 1; m <= SIZE; m++) {
                    fprintf(fp, "-%d%d%d ", i, j, k); 
                    fprintf(fp, "-%d%d%d ", i, j, m);
                    size += 1;
                    fprintf(fp,"0\n");
                }
            }
            fprintf(fp, "\n");
        }
    }
    //表示每一个位置只能填一个数字
    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k <= SIZE; k++) {
                fprintf(fp, "%d%d%d", i,k,j);
            }
            size += 1;
            fprintf(fp, "0");
            fprintf(fp, "\n");
        }
        fprintf(fp, "\n");
    }
    //表示每行
    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k < SIZE; k++) {
                for (int m = k + 1; m <= SIZE; m++) {
                    fprintf(fp, "-%d%d%d ", i, k,j );
                    fprintf(fp, "-%d%d%d ", i, m, j);
                    size += 1;
                    fprintf(fp, "0\n");
                }
            }
            fprintf(fp, "\n");
        }
    }
    //表示每行的数字不能重复
    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k <= SIZE; k++) {
                fprintf(fp, "%d%d%d", k,i , j);
            }
            size += 1;
            fprintf(fp, "0");
            fprintf(fp, "\n");
        }
        fprintf(fp, "\n");
    }
    //表示每列
    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k < SIZE; k++) {
                for (int m = k + 1; m <= SIZE; m++) {
                    fprintf(fp, "-%d%d%d ", k, i, j);
                    fprintf(fp, "-%d%d%d ", m, i, j);
                    size += 1;
                    fprintf(fp, "0\n");
                }
            }
            fprintf(fp, "\n");
        }
    }
    //表示每列数字不重复
    for (int m = 0; m < 3; m++) {
        for (int n = 0; n < 3; n++) {
            for (int i = 1; i <= 3; i++) {
                for (int j = 1; j <= 3; j++) {
                    for (int k = 1; k <= SIZE; k++) {
                        fprintf(fp, "%d%d%d ", i+m*3, j+n*3, k);
                    }
                    size += 1;
                    fprintf(fp, "0\n");
                }
            }//以上表示每个盒子可以填1~9
            fprintf(fp, "\n");
            for (int k = 1; k <= SIZE; k++) {
                
            }
        }
    }
    //表示每一个盒子
    
    
    return size;
}

int main() {
    FILE* fp;
    errno_t err = fopen_s( &fp, "temp.txt", "w");
    if (err != 0) {
        printf("fail to allocate memory\n");
        return -1;
    }
    int sudoku[SIZE][SIZE];
    generateSudokuPuzzle(sudoku, 1);
    //sudoku_to_cnf(sudoku, fp);
    printSudoku(sudoku);
    fclose(fp);
    return 0;
}