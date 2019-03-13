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

% matrix2array: array which elements are the elements of metrix : [4, 2, 4, 5, 6, 3, 5, 3, 5, 3]
array[1..k*s] of int: ArrNInseg =[NumInseg[i,j] | j in 1..s, i in 1..k] ;

% array which elements are set of int. it is used to to index each teching in a course in a semester : 
% [1..4, 5..6, 7..10, 11..15, 16..21, 22..24, 25..29, 30..32, 33..37, 38..40]
array[1..k*s] of set of int: indexInseg = [{k | k in sum([ArrNInseg[j] | j in 1..i-1])+1..sum([ArrNInseg[j] | j in 1..i])} | i in 1..k*s];

% number of teachings in a course per semester : [21, 19]
array[1..s] of int: InsgXsemestre =[ sum(j in 1..k) (NumInseg[j,i]) | i in 1..s];
% index of teaching per semester : [1..21, 22..40]
array[1..s] of set of int: indexInsgXsemestre = [{k | k in sum([InsgXsemestre[j] | j in 1..i-1])+1..sum([InsgXsemestre[j] | j in 1..i])} | i in 1..s];

% index of hours per semester : [1..40, 41..80]
array[1..s] of set of int: indexSemester = [{ k | k in  (i-1)*ore*days+1.. i*ore*days} | i in 1..s];
% index of hours per day : [1..8, 9..16, 17..24, 25..32, 33..40, 41..48, 49..56, 57..64, 65..72, 73..80]
array[1..s,1..days] of set of int: indexWeek = array2d(1..s,1..days, [ { k | k in  (i-1)*days*ore+(d-1)*ore+1..(i-1)*days*ore+d*ore}| i in 1..s, d in 1..days]);



int: totInseg = sum(j in 1..s) (InsgXsemestre[j]);

% for every teaching its hours of lecture
array[1..totInseg] of int: oreInsg = [4,4,4,5,5, 4,6,4,7,4 ,4,4,4,5,3, 4,5,4,6,4   ,4 ,5,4,5,3, 4,5,4,6,4 ,4,3,4,5,5, 4,6,4,3,4];

% 2 teaching per teacher 
array[1..s,1..p] of int: pInsg=[|
5,4,11,3,9,   7,13,20,15,18, 39,8,17,28,25, 31,33,27,26,24,|
2,32,21,40,37,  38,6,1,10,12, 36,35,22,30,29, 16,14,19,34,23,|
|];

% for each teaching the students who follow it
array[1..totInseg] of int: NumStud = 
[150,80,190,100,130, 50,50,70,190,120, 50,80,190,100,130, 150,50,70,190,120, 50,80,190,100,130, 50,50,70,190,120, 50,80,190,100,130, 50,50,70,190,120 ];

array[1..totInseg,1..s*ore*days] of var 0..n: orario;

constraint % constraint: if number of student of a teaching are > of capacity of room then for each t  teaching couldn't be held there
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i],a in 1..n) (
      if NumStud[c] > CapAule[a] then
        forall( t in indexSemester[i] ) (
          orario[c,t] != a
        )
      else true
      endif
    )
  ) 
  /\
  forall( i in 1..k*s ) (
    forall(c1,c2 in indexInseg[i] where c1<c2,t in 1..s*ore*days) (
        bool2int(orario[c1,t]>0) + bool2int(orario[c2,t]>0) <=1
    )
  )
  /\ % constraint: sum of all hours in a semester about every teaching in that semester must be equal to requirement
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i]) (
      sum( [bool2int(orario[c,t]>0) | t in indexSemester[i]]) = oreInsg[c]
    )
  )
  /\ % constraint: in one day number of hours of a teching should be betwen 2<= sum() >=4 if there is a teaching in that day else sum is 0 and the model is unsatisfable
  forall( j in 1..s) (
    forall(i in indexInsgXsemestre[j],d in 1..days) (
      if sum([ bool2int(orario[i,t]>0) | t in indexWeek[j,d]]) >0 then
        sum([bool2int(orario[i,t]>0) | t in indexWeek[j,d]]) >=2 
        /\
        sum([bool2int(orario[i,t]>0) | t in indexWeek[j,d]]) <=4
      else true
      endif
    )
  )
  /\% constraint: in one day number of hours of a teaching held from a teacher should be betwen 2<= sum() >=4  and for every hour he couldn't teach in two room
  forall(i in 1..p, j in 1..s) (
    if pInsg[1,i] in indexInsgXsemestre[j] /\ pInsg[2,i] in indexInsgXsemestre[j] then
      forall(d in 1..days) (
        sum([bool2int(orario[pInsg[1,i],t]>0) + bool2int(orario[pInsg[2,i],t]>0) | t in indexWeek[j,d]]) <=4 
      ) 
      /\
      forall(t in indexSemester[j]) (
        sum([bool2int(orario[pInsg[1,i],t]>0) + bool2int(orario[pInsg[2,i],t]>0)]) <=1
      )
    else true   
    endif   
  )
  /\
  forall(i in 1..s) ( % non si può usare alldifferent per la presenza dei 0
    forall( t in indexSemester[i],c1,c2 in indexInsgXsemestre[i]) (
      if orario[c1,t]>0 /\ orario[c2,t]>0 /\ c1 != c2 then % c1 != c2 importante!!! non ci si pensa ma c1 e c2 nell'insieme possono  
        orario[c1,t] != orario[c2,t]                       % assumere anche gli stessi valori e dunque si ha una MODEL UNSATISFIABLE
      else true
      endif
    ) 
  )
  /\ % constraint: lenght of a teaching in a room should be at least 2 hours
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i],d in 1..days) (
      forall(t in indexWeek[i,d]) (
        if  orario[c,t]>0 then
          if t mod ore != 0  then 
            if t-1 mod ore != 0 then 
              orario[c,t] = orario[c,t+1] \/ orario[c,t] = orario[c,t-1] 
            else orario[c,t] = orario[c,t+1] 
            endif
          else orario[c,t] = orario[c,t-1] 
          endif
        else true
        endif
      )
    )
  )
;

%solve satisfy;
solve :: int_search([orario[c,t] | c in 1..totInseg, t in 1..s*days*ore], first_fail, indomain_random, complete) satisfy;


output[ 
    if j ==1 then
      if i =InsgXsemestre[1]+1 then 
        "\n\n m"++show(i)++"\t" 
      else if i <InsgXsemestre[1]+1 then "\n m"++show(i)++"\t  "++show(orario[i,j]) else "\n m"++show(i)++"\t"  endif 
      endif
    else
      if i<InsgXsemestre[1]+1 /\ j <=days*ore then
        if (j-1) mod ore == 0 then "  " else "" endif ++show(orario[i,j])
      else 
        if i>=InsgXsemestre[1]+1 /\ j >days*ore then
          if (j-1) mod ore == 0 then "  " else "" endif ++show(orario[i,j])
        else ""
        endif
      endif
    endif   
    
| i in 1..totInseg, j in 1..s*ore*days
];



