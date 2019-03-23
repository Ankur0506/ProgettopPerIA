int: p = 20; % number of prof.
int: s=2; % semesters
int: n =3; % number of room
int: ore = 8; % hours per day of teaching
int: days = 5; % days of teaching in a week
array[1..n] of int: CapAule =[100,150,200]; % capacity of rooms
int: k =5; % numeber of courses
array[1..k,1..s] of int: NumInseg=[| % Input matrix of teachings where lines are courses and semesters columns
4,3|
2,5|
4,3|
5,5|
6,3|
|];

array[1..k*s] of int: ArrNInseg =[NumInseg[i,j] | j in 1..s, i in 1..k] ;

array[1..k*s] of set of int: indexInseg = [{k | k in sum([ArrNInseg[j] | j in 1..i-1])+1..sum([ArrNInseg[j] | j in 1..i])} | i in 1..k*s];

array[1..s] of int: InsgXsemestre =[ sum(j in 1..k) (NumInseg[j,i]) | i in 1..s];

array[1..s] of set of int: indexInsgXsemestre = [{k | k in sum([InsgXsemestre[j] | j in 1..i-1])+1..sum([InsgXsemestre[j] | j in 1..i])} | i in 1..s];

array[1..s] of set of int: indexSemestre = [{ k | k in  (i-1)*ore*days+1.. i*ore*days} | i in 1..s];

%array[1..s*days] of set of int: indexWeek = [{ k | k in  (i-1)*ore+1.. i*ore} | i in 1..s*days];
%array[1..s,1..days] of set of int: x = array2d(1..s,1..days, [ indexWeek[(i-1)*days+d]| i in 1..s, d in 1..days]);

array[1..s,1..days] of set of int: x = array2d(1..s,1..days, [ { k | k in  (i-1)*days*ore+(d-1)*ore+1..(i-1)*days*ore+d*ore}| i in 1..s, d in 1..days]);

output[show(ArrNInseg)];
output["\n indici insegnamenti per corso\n"++show(indexInseg)];
output["\n numero di insegnamenti per semestre\n "++show(InsgXsemestre)];
output["\n indici per numero di insegnamenti per semestre \n"++show(indexInsgXsemestre)];
output["\n ore per semestre \n"++show(indexSemestre)];
%output["\n"++show(indexWeek)];
output["\n ore per giorno\n"++show(x)];
