#!/bin/bash

if [ $# -ne 2 ]; then
	echo "usage: $0 <#pidgeons> <#holes>" >&2
	exit 1
fi

N=$1
M=$2

# v i j
v() {
	local i=$1
	local j=$2
	printf "%d" $((1+i+N*j))
}

printf "c Pidgeonhole with %d pidgeons and %d holes\n" $N $M
printf "p cnf %d %d\n" $(v $N $M) $((N+M*N*(N-1)/2))

# All pidgeons in some hole
# /\_i \/_j p_ij
for i in `seq 1 $N`; do
	for j in `seq 1 $M`; do
		printf "%d " $(v $i $j)
	done
	printf "0\n"
done

# Max. one pidgeon per hole
for j in `seq 1 $M`; do
	for i1 in `seq 1 $N`; do
		for i2 in `seq $((i1+1)) $N`; do
			printf "%d %d 0\n" -$(v $i1 $j) -$(v $i2 $j)
		done
	done
done
