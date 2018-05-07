#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>

#include "sat.h"

#define BUF_LEN 50

void setstdout (int *pipefd) {
  close(pipefd[0]);
  dup2(pipefd[1], 1);
}

void callsat (int *pipefd) {
  char *args[] = {"z3", "in.smt2"};
  setstdout(pipefd);
  if (execvp(args[0],args) < 0)
    exit(2);
}

int getresult (pid_t pid, int *pipefd) {
  char resstr[BUF_LEN];

  close(pipefd[1]);
  wait(NULL);
  read(pipefd[0],resstr,BUF_LEN);
  close(pipefd[0]);
  if (strcmp(resstr,"sat\n") == 0)
    return 1;
  else if (strcmp(resstr,"unsat\n") == 0)
    return 0;
  else
    exit(2);
}

int forkchild (void) {
  pid_t pid;
  int pipefd[2];

  if (pipe(pipefd) < 0)
    exit(2);

  pid = fork();

  if (pid < 0)
    exit(2);
  else if (pid == 0)
    callsat(pipefd);
  else
    return getresult(pid,pipefd);

  return 2; // never gets called
}

int runsat (void) {
  return forkchild();
}


//int main(int argc, char* argv[]) {
//  return runsat();
//}
