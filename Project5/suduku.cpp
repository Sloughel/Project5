#include"stu.h"
void printSudoku(int sudoku[SIZE][SIZE]);
bool isValid(int sudoku[SIZE][SIZE], int row, int col, int num);
void generateSudokuPuzzle(int puzzle[SIZE][SIZE], int holes,int answer[SIZE][SIZE]);
void copySudoku(int dest[SIZE][SIZE], int src[SIZE][SIZE]);
bool generateFullSudoku(int sudoku[SIZE][SIZE]);
int solveSudokuCount(int sudoku[SIZE][SIZE], int maxSolutions);
FILE* open_a_file(const char* filename);
void play_the_sudoku(int puzzle[SIZE][SIZE], int answer[SIZE][SIZE], int holes);
int  sudoku_format(int sudoku[SIZE][SIZE], FILE* fp);

void sudoku_to_cnf(int size) {
    FILE* input=NULL;
    FILE* out = NULL;
    int temp;
    int i, j, k;
    int num=0;
    int sign = 1;
    errno_t err = fopen_s(&input, "temp.txt", "r");
    if (err != 0)goto error;
    err = fopen_s(&out, "input\\sudoku.cnf", "w");
    if (err != 0)goto error;
    fprintf(out, "p cnf 729 %d\n",size);
    for (num = 0; num < size; num++) {
        temp = get_num_from_file(input);
        if (temp >= 0)sign = 1;
        else sign = -1;
        temp = abs(temp);
        if ((temp < 111 || temp>999) && temp != 0)
            goto error;
        i = temp / 100, j = (temp / 10) % 10, k = temp % 10;
        if (temp == 0)fprintf(out, "0\n");
        else {
            if (sign == -1)fprintf(out, "-");
            fprintf(out, "%d ", (i - 1) * 81 + (j - 1) * 9 + k);
        }
    }
    fclose(input);
    fclose(out);
    return;
error:
    printf("fail to open the fail\n");
    if (input != NULL)fclose(input);
    if (out != NULL)fclose(out);
    exit(-1);

}
bool sudoku_test() {
    FILE* fp;
    fp = open_a_file("temp.txt");
    int puzzle[SIZE][SIZE];
    int answer[SIZE][SIZE];
    int holes; 
    int difficulty = 0;
    int size;
    printf("请输入难度：（1，2，3）:");
    if((scanf_s("%d", &difficulty)) != 1 || difficulty > 3 || difficulty < 1) {
        printf("wrong input!\n");
        printf("您输入的难度不正确\n");
        return false;
    }
    switch (difficulty) {
    case 1: holes = 3; break; // 简单
    case 2: holes = 40; break; // 中等
    case 3: holes = 50; break; // 困难
    default: holes = 35; // 默认
    } // 根据难度确定挖洞数量（难度越高，挖洞越多）

    generateSudokuPuzzle(puzzle, holes,answer);
    size=sudoku_format(puzzle, fp);
    fclose(fp);
    sudoku_to_cnf(size);
    play_the_sudoku(puzzle,answer,holes);
    
    printSudoku(answer);
   
    return true;
}

void generateSudokuPuzzle(int puzzle[SIZE][SIZE], int holes,int answer[SIZE][SIZE]) { // 挖洞法生成数独谜题

    srand(time(0));//初始化随机器

    for (int i = 0; i < SIZE; i++)
        for (int j = 0; j < SIZE; j++)
            puzzle[i][j] = EMPTY;  // 初始化数独为空

    generateFullSudoku(puzzle);// 生成完整数独
    copySudoku(answer, puzzle);


    


    int temp[SIZE][SIZE];
    copySudoku(temp, puzzle); // 复制一份用于挖洞测试

    int count = 0;
    // 随机挖洞，确保至少有一个解且解唯一
    while (count < holes) {
        int row = rand() % SIZE;
        int col = rand() % SIZE;


        if (temp[row][col] == EMPTY)  continue;// if it's EMPTY,continue



        int value = temp[row][col]; // 保存当前值，用于恢复
        temp[row][col] = EMPTY;//assign it EMPTY


        int solutions = solveSudokuCount(temp, 2); // 检查解的数量，最多检查2个解


        if (solutions == 1) {
            puzzle[row][col] = EMPTY;
            count++;
        }  // 如果解唯一，保留这个洞
        else
            temp[row][col] = value;// 否则恢复该值

    }
}

bool isRowValid(int sudoku[SIZE][SIZE], int row, int num) {
    for (int col = 0; col < SIZE; col++) 
        if (sudoku[row][col] == num) 
            return false;
        
    return true;
}
bool isColValid(int sudoku[SIZE][SIZE], int col, int num) {
    for (int row = 0; row < SIZE; row++) 
        if (sudoku[row][col] == num) 
            return false;
        
    return true;
}
bool isBoxValid(int sudoku[SIZE][SIZE], int startRow, int startCol, int num) {
    for (int row = 0; row < 3; row++) 
        for (int col = 0; col < 3; col++) 
            if (sudoku[startRow + row][startCol + col] == num) 
                return false;
            
    return true;
}


bool isPercentValid(int sudoku[SIZE][SIZE], int row, int col, int num) {
    
    if (row == SIZE-1-col) {
        for (int i = 0; i < SIZE; i++) {
            if (i == row) continue;
            if (sudoku[i][SIZE-1-i] == num) 
                return false;
            
        }
    }
    bool window1 = true;
    bool window2 = true;
    if ((row >= 1 && row <= 3) && (col >= 1 && col <= 3)) window1 = isBoxValid(sudoku, 1, 1, num);
    if ((row >= 5 && row <= 7) && (col >= 5 && col <= 7)) window2 = isBoxValid(sudoku, 5, 5, num);
  

    return window1&&window2;
}
bool isValid(int sudoku[SIZE][SIZE], int row, int col, int num) { // 检查数字在当前位置是否合法
    return isRowValid(sudoku, row, num) &&
        isColValid(sudoku, col, num) &&
        isBoxValid(sudoku, row - row % 3, col - col % 3, num)&&
        isPercentValid(sudoku,row,col,num);
}


bool findEmptyLocation(int sudoku[SIZE][SIZE], int* row, int* col) {// 寻找下一个空白位置
    for (*row = 0; *row < SIZE; (*row)++) 
        for (*col = 0; *col < SIZE; (*col)++) 
            if (sudoku[*row][*col] == EMPTY) return true;
            
    return false;
}


int solveSudokuCount(int sudoku[SIZE][SIZE], int maxSolutions) {// 求解数独并统计解的数量
    int row, col;

    if (!findEmptyLocation(sudoku, &row, &col)) return 1; // 如果没有空白位置，找到一个解
    
    int solutions = 0;

    for (int num = 1; num <= SIZE; num++) {   // 尝试填入1-9
        if (isValid(sudoku, row, col, num)) {
            sudoku[row][col] = num;

            solutions += solveSudokuCount(sudoku, maxSolutions - solutions); // 递归求解

            if (solutions >= maxSolutions) {// 如果解的数量超过maxSolutions，提前返回
                sudoku[row][col] = EMPTY; // 回溯
                return solutions;
            }

            sudoku[row][col] = EMPTY; // 回溯
        }
    }

    return solutions;
}


bool generateFullSudoku(int sudoku[SIZE][SIZE]) {// 生成完整的数独终盘
    int row, col;

    
    if (!findEmptyLocation(sudoku, &row, &col)) 
        return true;// 如果没有空白位置，数独完成

    int nums[SIZE] = { 1, 2, 3, 4, 5, 6, 7, 8, 9 };
    for (int i = SIZE - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        int temp = nums[i];
        nums[i] = nums[j];
        nums[j] = temp;
    }// 随机排列1-9

   
    for (int i = 0; i < SIZE; i++) {
        int num = nums[i];
        if (isValid(sudoku, row, col, num)) {
            sudoku[row][col] = num; // 尝试填入数字

            if (generateFullSudoku(sudoku)) return true; // 递归生成
            
            sudoku[row][col] = EMPTY; // 回溯
        }
    }

    return false; // 用于回溯
}

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
void copySudoku(int dest[SIZE][SIZE], int src[SIZE][SIZE]) {
    for (int i = 0; i < SIZE; i++)
        for (int j = 0; j < SIZE; j++)
            dest[i][j] = src[i][j];
}

FILE* open_a_file(const char* filename) {
    FILE* fp;
    errno_t err = fopen_s(&fp, "temp.txt", "w");
    if (err != 0) {
        printf("fail to allocate memory\n");
        return NULL;
    }
    return fp;
}

int  sudoku_format(int sudoku[SIZE][SIZE], FILE* fp) {
    int size = 0;

    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k <= SIZE; k++) {
                fprintf(fp, "%d%d%d ", i, j, k);
            }
            fprintf(fp, "0"); size += 1;
            fprintf(fp, "\n");
        }
        fprintf(fp, "\n");
    } //表示每一个位置都可以填一到九这九个数字

    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k < SIZE; k++) {
                for (int m = k + 1; m <= SIZE; m++) {
                    fprintf(fp, "-%d%d%d ", i, j, k);
                    fprintf(fp, "-%d%d%d ", i, j, m);
                    size += 1;
                    fprintf(fp, "0\n");
                }
            }
            fprintf(fp, "\n");
        }
    } //表示每一个位置只能填一个数字

    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k <= SIZE; k++) {
                fprintf(fp, "%d%d%d ", i, k, j);
            }
            size += 1;
            fprintf(fp, "0");
            fprintf(fp, "\n");
        }
        fprintf(fp, "\n");
    } //表示每行

    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k < SIZE; k++) {
                for (int m = k + 1; m <= SIZE; m++) {
                    fprintf(fp, "-%d%d%d ", i, k, j);
                    fprintf(fp, "-%d%d%d ", i, m, j);
                    size += 1;
                    fprintf(fp, "0\n");
                }
            }
            fprintf(fp, "\n");
        }
    } //表示每行的数字不能重复

    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = 1; k <= SIZE; k++) {
                fprintf(fp, "%d%d%d ", k, i, j);
            }
            size += 1;
            fprintf(fp, "0");
            fprintf(fp, "\n");
        }
        fprintf(fp, "\n");
    } //表示每列

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
    } //表示每列数字不重复

    for (int m = 0; m < 3; m++) {
        for (int n = 0; n < 3; n++) {
            for (int i = 1; i <= 3; i++) {
                for (int j = 1; j <= 3; j++) {
                    for (int k = 1; k <= SIZE; k++) {
                        fprintf(fp, "%d%d%d ", i + m * 3, j + n * 3, k);
                    }
                    size += 1;
                    fprintf(fp, "0\n");
                }
            }//以上表示每个盒子可以填1~9
            fprintf(fp, "\n");
            for (int i = 1; i <= 3; i++) {
                for (int j = 1; j <= 3; j++) {
                    for (int l = 1; l <= 3; l++) {
                        for (int p = 1; p <= 3; p++) {
                            for (int k = 1; k <= SIZE; k++) {
                                if (i != l && j != p) {
                                    fprintf(fp, "-%d%d%d ", i+m*3, j+n*3, k);
                                    fprintf(fp, "-%d%d%d ", l+m*3, p+n*3, k);
                                    fprintf(fp, "0\n");
                                    size += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }  //表示每一个盒子

    for (int i = 1; i <= SIZE; i++) {
        for (int j = 1; j <= SIZE; j++) {
            for (int k = i+1; k <= SIZE; k++) {
                
                    fprintf(fp, "-%d%d%d ", i,SIZE-i , j);
                    fprintf(fp, "-%d%d%d ", k,SIZE-k , j);
                    size += 1;
                    fprintf(fp, "0\n");
                
            }
            fprintf(fp, "\n");
        }
    }//表示反对角不能有相同的

    for (int i = 1; i <= 3; i++) {
        for (int j = 1; j <= 3; j++) {
            for (int l = 1; l <= 3; l++) {
                for (int p = 1; p <= 3; p++) {
                    for (int k = 1; k <= SIZE; k++) {
                        if (i != l && j != p) {
                            fprintf(fp, "-%d%d%d ", i + 1, j + 1, k);
                            fprintf(fp, "-%d%d%d ", l + 1, p + 1, k);
                            fprintf(fp, "0\n");
                            size += 1;
                        }
                    }
                }
            }
        }
    }//表示左上盒子


    for (int i = 1; i <= 3; i++) {
        for (int j = 1; j <= 3; j++) {
            for (int l = 1; l <= 3; l++) {
                for (int p = 1; p <= 3; p++) {
                    for (int k = 1; k <= SIZE; k++) {
                        if (i != l && j != p) {
                            fprintf(fp, "-%d%d%d ", i + 5, j + 5, k);
                            fprintf(fp, "-%d%d%d ", l + 5, p + 5, k);
                            fprintf(fp, "0\n");
                            size += 1;
                        }
                    }
                }
            }
        }
    }//表示右下盒子

    for (int i = 0; i < SIZE; i++) {
        for (int j = 0; j < SIZE; j++) {
            if (sudoku[i][j] != EMPTY) {
                fprintf(fp, "%d%d%d ", i + 1, j + 1, sudoku[i][j]);
                fprintf(fp, "0\n");
                size += 1;
            }
        }
    }//表示已知的提示词
    return size;
}

bool is_right(int sudoku[SIZE][SIZE], int answer[SIZE][SIZE]) {
    for (int i = 0; i < SIZE; i++)
        for (int j = 0; j < SIZE; j++)
            if (sudoku[i][j] != answer[i][j]) return false;
    return true;
}
void show_playing(int puzzle[SIZE][SIZE], int player_sudoku[SIZE][SIZE]) {

    printf("--------------------\n");
    for (int i = 0; i < SIZE; i++) {
        if (i % 3 == 0 && i != 0)
            printf("------+-------+------\n");

        for (int j = 0; j < SIZE; j++) {
            if (j % 3 == 0 && j != 0)
                printf("| ");

            if (puzzle[i][j] == EMPTY) {
                if (player_sudoku[i][j] == EMPTY)printf("  ");
                else printf("\033[32m""%d " "\033[0m", player_sudoku[i][j]);//用户所填的数字显示为绿色
            }

            else printf("%d ", puzzle[i][j]);

        }
        printf("\n");
    }
    printf("--------------------\n");

}
void play_the_sudoku(int puzzle[SIZE][SIZE], int answer[SIZE][SIZE], int holes) {
    int player_sudoku[SIZE][SIZE];
    copySudoku(player_sudoku, puzzle);//常见一个当前数独游戏格局的模板用以游戏

    int x, y, num;
    printSudoku(player_sudoku);//先展示游戏格局

    while (holes > 0) {

        printf("请填写：");
        scanf_s("%d%d%d", &y, &x, &num);
        bool is_suit = (y >= 1 && y <= 9) && (x >= 1 && x <= 9) && (num >= 1 && num <= 9);
        if (is_suit && puzzle[x - 1][y - 1] == EMPTY) {
            system("cls");
            player_sudoku[x - 1][y - 1] = num;
            holes--;
        }
        else {
            system("cls");
            printf("wrong input,it has a num here or the input is beyond the limit!\n");
        }
        show_playing(puzzle, player_sudoku);
        if (holes == 0) {
            if (is_right(player_sudoku, answer))printf("正确\n");
            else {
                printf("错误\n");
                holes++;
            }
        }
    }

    
}
