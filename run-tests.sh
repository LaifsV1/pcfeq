#!/bin/bash

LOGS_DIR=logs

mkdir $LOGS_DIR

LOG_SAFE=equiv.log
LOG_UNSAFE=inequiv.log
LOG_MISC=misc.log

DFS=dfs_
BFS=bfs_
STDOUT=out_
STDERR=err_
FILES=files_
STATUS=status_

DFS_SAFE=$STDOUT$DFS$LOG_SAFE
DFS_UNSAFE=$STDOUT$DFS$LOG_UNSAFE
DFS_MISC=$STDOUT$DFS$LOG_MISC
BFS_SAFE=$STDOUT$BFS$LOG_SAFE
BFS_UNSAFE=$STDOUT$BFS$LOG_UNSAFE
BFS_MISC=$STDOUT$BFS$LOG_MISC

FILES_DFS_SAFE=$FILES$DFS$LOG_SAFE
FILES_DFS_UNSAFE=$FILES$DFS$LOG_UNSAFE
FILES_DFS_MISC=$FILES$DFS$LOG_MISC
FILES_BFS_SAFE=$FILES$BFS$LOG_SAFE
FILES_BFS_UNSAFE=$FILES$BFS$LOG_UNSAFE
FILES_BFS_MISC=$FILES$BFS$LOG_MISC

TIMES_DFS_SAFE=$STDERR$DFS$LOG_SAFE
TIMES_DFS_UNSAFE=$STDERR$DFS$LOG_UNSAFE
TIMES_DFS_MISC=$STDERR$DFS$LOG_MISC
TIMES_BFS_SAFE=$STDERR$BFS$LOG_SAFE
TIMES_BFS_UNSAFE=$STDERR$BFS$LOG_UNSAFE
TIMES_BFS_MISC=$STDERR$BFS$LOG_MISC

STATUS_DFS_SAFE=$STATUS$DFS$LOG_SAFE
STATUS_DFS_UNSAFE=$STATUS$DFS$LOG_UNSAFE
STATUS_DFS_MISC=$STATUS$DFS$LOG_MISC
STATUS_BFS_SAFE=$STATUS$BFS$LOG_SAFE
STATUS_BFS_UNSAFE=$STATUS$BFS$LOG_UNSAFE
STATUS_BFS_MISC=$STATUS$BFS$LOG_MISC

PROGRAMS_ROOT=programs

UNSAFE_PATH=$PROGRAMS_ROOT/inequiv
SAFE_PATH=$PROGRAMS_ROOT/equiv
MISC_PATH=$PROGRAMS_ROOT/misc

RED='\033[0;31m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
DEFAULT='\033[0m'



declare -A SPECIAL_BOUNDS

SPECIAL_BOUNDS=(
    ["fun_pairs.pbl"]="9"
    ["mccarthy-knuth.pbl"]="8"
    ["fix_curried_ineq.pbil"]="24"
    ["fix_uncurried_ineq.pbil"]="35"
    ["pitts-3.14.pbl"]="65"
    ["fix_curried2_ineq.pbil"]="22"
    ["nt_1st-aug-22_ineq_1.pbl"]="60"
    ["nt_1st-aug-22_ineq_2_1.pbl"]="42"
    ["nt_1st-aug-22_ineq_2.pbl"]="33"
    ["v-stacks.pbl"]="14"
    ["v-stacks-nonlinear.pbl"]="19"
)


print_check_message () {
    printf "checking ${CYAN}${BOLD}$1${DEFAULT} with bound ${CYAN}${BOLD}$2${DEFAULT}..."
}
print_header () {
    START=${#1}
    END=65
    
    printf "\n${CYAN}<><>${DEFAULT}"
    printf "${BOLD}Running $1${DEFAULT}"

    for (( c=$START; c<=$END; c=$c+2 ))
    do
        printf "${CYAN}<>${DEFAULT}"
    done
    
    printf "\n"
}
print_log () {
    printf "\n$1 result in file: ${BOLD}%s${DEFAULT}\n" $2
}

total_checked=0
eq_proved_num=0
ineq_proved_num=0
inconclusive_num=0
error_num=0

run_test () {
    print_header "$1"
    
    for file in $2/*
    do
        filename=$(basename $file)
        [ ${SPECIAL_BOUNDS["$filename"]+abc} ] && BOUND=${SPECIAL_BOUNDS["$filename"]} || BOUND=20
        
        print_check_message $file $BOUND

        echo $filename >> $6
        
        OUTPUT=$((time timeout 150s ./pcfeq.native -i $file -b $BOUND) 2>> $5)
        EXIT_CODE=$?
        
        if [ $EXIT_CODE -eq 0 ]
        then
            echo -e "\u001b[33minconclusive\033[0m"
            echo "N/A" >> $7
            let "inconclusive_num+=1"
        elif [ $EXIT_CODE -eq 42 ]
        then
            echo -e "\033[1;33minequivalent\033[0m"
            echo "no" >> $7
            let "ineq_proved_num+=1"
        elif [ $EXIT_CODE -eq 43 ]
        then
            echo -e "\033[1;32mequivalent\033[0m"
            echo "yes" >> $7
            let "eq_proved_num+=1"
        else
            echo -e "\033[1;31merror\033[0m"
            echo "error" >> $7
            let "error_num+=1"
        fi

        let "total_checked+=1"
        
        printf "$OUTPUT\n\n\n\n"  >> $3
    done
    print_log "$1" $3
}

TIMEFORMAT=%R
#let "eq_proved_num=0"
#let "ineq_proved_num=0"
#let "inconclusive_num=0"
#let "error_num=0"
#run_test "DFS Sanity Tests" ${MISC_PATH} $DFS_MISC 1 $TIMES_DFS_MISC $FILES_DFS_MISC $STATUS_DFS_MISC
#run_test "DFS Equivalence Checks" ${SAFE_PATH} $DFS_SAFE 1 $TIMES_DFS_SAFE $FILES_DFS_SAFE $STATUS_DFS_SAFE
#run_test "DFS Inequivalence Checks" ${UNSAFE_PATH} $DFS_UNSAFE 1 $TIMES_DFS_UNSAFE $FILES_DFS_UNSAFE $STATUS_DFS_UNSAFE
#echo -e "\033[1;32m*** $(eq_proved_num) equivalences proved\033[0m"
#echo -e "\033[1;33m*** $(ineq_proved_num) inequivalences proved\033[0m"
#echo -e "\u001b[33m*** $(inconclusive_num) inconclusive examples\033[0m"
#echo -e "\033[1;31m*** $(error_num) error(s) in programs\033[0m"

run_test_arg () {
    DIR=$LOGS_DIR/$1
    
    mkdir $DIR

    rm -f $DIR/$DFS_SAFE
    rm -f $DIR/$DFS_UNSAFE
    rm -f $DIR/$DFS_MISC
    rm -f $DIR/$BFS_SAFE
    rm -f $DIR/$BFS_UNSAFE
    rm -f $DIR/$BFS_MISC

    rm -f $DIR/$FILES_DFS_SAFE
    rm -f $DIR/$FILES_DFS_UNSAFE
    rm -f $DIR/$FILES_DFS_MISC
    rm -f $DIR/$FILES_BFS_SAFE
    rm -f $DIR/$FILES_BFS_UNSAFE
    rm -f $DIR/$FILES_BFS_MISC

    rm -f $DIR/$TIMES_DFS_SAFE
    rm -f $DIR/$TIMES_DFS_UNSAFE
    rm -f $DIR/$TIMES_DFS_MISC
    rm -f $DIR/$TIMES_BFS_SAFE
    rm -f $DIR/$TIMES_BFS_UNSAFE
    rm -f $DIR/$TIMES_BFS_MISC

    rm -f $DIR/$STATUS_DFS_SAFE
    rm -f $DIR/$STATUS_DFS_UNSAFE
    rm -f $DIR/$STATUS_DFS_MISC
    rm -f $DIR/$STATUS_BFS_SAFE
    rm -f $DIR/$STATUS_BFS_UNSAFE
    rm -f $DIR/$STATUS_BFS_MISC
    
    # run_test "BFS Sanity Tests" ${MISC_PATH} $DIR/$BFS_MISC 0 $DIR/$TIMES_BFS_MISC $DIR/$FILES_BFS_MISC $DIR/$STATUS_BFS_MISC $2
    
    run_test "BFS Equivalence Checks" ${SAFE_PATH} $DIR/$BFS_SAFE 0 $DIR/$TIMES_BFS_SAFE $DIR/$FILES_BFS_SAFE $DIR/$STATUS_BFS_SAFE $2
    echo -e "\033[1;32m*** ${eq_proved_num} equivalences proved\033[0m"
    echo -e "\u001b[34;1m*** ${total_checked} files checked\033[0m"
    
    run_test "BFS Inequivalence Checks" ${UNSAFE_PATH} $DIR/$BFS_UNSAFE 0 $DIR/$TIMES_BFS_UNSAFE $DIR/$FILES_BFS_UNSAFE $DIR/$STATUS_BFS_UNSAFE $2

    echo -e "\033[1;32m*** ${eq_proved_num} equivalences proved\033[0m"
    echo -e "\033[1;33m*** ${ineq_proved_num} inequivalences proved\033[0m"
    echo -e "\u001b[33m*** ${inconclusive_num} inconclusive examples\033[0m"
    echo -e "\033[1;31m*** ${error_num} error(s) in programs\033[0m"
    echo -e "\u001b[34;1m*** ${total_checked} files checked\033[0m"

    let "eq_proved_num=0"
    let "ineq_proved_num=0"
    let "inconclusive_num=0"
    let "error_num=0"
    let "total_checked=0"
}

O_DEF=""

F_DEF=default

run_test_arg $F_DEF $O_DEF
