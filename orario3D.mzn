int: p = 6;
int: s=2;
int: n =3;
int: ore = 5;
int: days = 2;
array[1..n] of int: CapAule =[100,150,200];
int: k =3;
array[1..k,1..s] of int: NumInseg=[|
2,2|
1,3|
3,1|
|];

array[1..k*s] of int: ArrNInseg =[NumInseg[i,j] | j in 1..s, i in 1..k] ;

array[1..k*s] of set of int: indexInseg = [{k | k in sum([ArrNInseg[j] | j in 1..i-1])+1..sum([ArrNInseg[j] | j in 1..i])} | i in 1..k*s];

array[1..s] of int: InsgXsemestre =[ sum(j in 1..k) (NumInseg[j,i]) | i in 1..s];

array[1..s] of set of int: indexInsgXsemestre = [{k | k in sum([InsgXsemestre[j] | j in 1..i-1])+1..sum([InsgXsemestre[j] | j in 1..i])} | i in 1..s];


array[1..s] of set of int: indexSemester = [{ k | k in  (i-1)*ore*days+1.. i*ore*days} | i in 1..s];

array[1..s,1..days] of set of int: indexWeek = array2d(1..s,1..days, [ { k | k in  (i-1)*days*ore+(d-1)*ore+1..(i-1)*days*ore+d*ore}| i in 1..s, d in 1..days]);


int: totInseg = sum(j in 1..s) (InsgXsemestre[j]);

array[1..totInseg] of int: oreInsg = [4,2,4,2,5,3, 4,2,4,3,2,4];

array[1..s,1..p] of int: pInsg=[|
5,4,11,3,9,7|
2,8,6,1,10,12,|
|];

array[1..totInseg] of int: NumStud = [150,100,80,190,50,130, 50,150,50,170,190,120];

array[1..totInseg,1..s*ore*days,1..n] of var 0..1: orario;

constraint % constraint: 
  forall( i in 1..k*s ) (
    forall(c1,c2 in indexInseg[i] where c1<c2,t in 1..s*ore*days) (
        sum([orario[c1,t,a] + orario[c2,t,a]| a in 1..n]) <=1
    )
  )
  /\ % constraint: one teaching can be held only in a room at the same time
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i], t in indexSemester[i]) (
      sum( [orario[c,t,a] | a in 1..n]) <=1
    )
  )
  /\ % constraint: sum of all hours in a semester about every teaching in that semester must be equal to requirement
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i]) (
      sum( [orario[c,t,a] | a in 1..n, t in indexSemester[i]]) = oreInsg[c]
    )
  )
  /\ % constraint: for each room and each hour just one of teaching can be held
  forall(i in 1..s) (
    forall(a in 1..n, t in indexSemester[i]) (
      sum([orario[c,t,a] | c in indexInsgXsemestre[i]]) <=1
    )
  )
  /\ % constraint: in one day number of hours of a teching should be betwen 2<= sum() >=4 if there is a teaching in that day else sum is 0 and the model is unsatisfable
  forall( j in 1..s) (
    forall(i in indexInsgXsemestre[j],d in 1..days) (
      if sum([ orario[i,t,a] | t in indexWeek[j,d], a in 1..n]) >0 then
        sum([ orario[i,t,a] | t in indexWeek[j,d], a in 1..n]) >=2 
        /\
        sum([ orario[i,t,a] | t in indexWeek[j,d], a in 1..n]) <=4
      else true
      endif
    )
  )
  /\% constraint: in one day number of hours of a teaching held from a teacher should be betwen 2<= sum() >=4  and for every hour he couldn't teach in two room
  forall(i in 1..p, j in 1..s) (
    if pInsg[1,i] in indexInsgXsemestre[j] /\ pInsg[2,i] in indexInsgXsemestre[j] then
      forall(d in 1..days) (
        sum([orario[pInsg[1,i],t,a] +orario[pInsg[2,i],t,a] | t in indexWeek[j,d], a in 1..n]) <=4 
      ) 
      /\
      forall(t in indexSemester[j]) (
        sum([orario[pInsg[1,i],t,a] +orario[pInsg[2,i],t,a] | a in 1..n]) <=1
      )
    else true   
    endif   
  )
  /\% constraint: if number of student of a teaching are > then capacity of room then for each t  teaching couldn't be held there
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i],a in 1..n) (
      if NumStud[c] > CapAule[a] then
        forall( t in indexSemester[i] ) (
          orario[c,t,a] < 1
        )
      else true
      endif
    )
  )
  /\ % constraint: lenght of a teaching in a room should be at least 2 hours
  forall(i in 1..s) (
    forall(c in indexInsgXsemestre[i],d in 1..days) (
      forall(t in indexWeek[i,d],a in 1..n) (
        if  orario[c,t,a]>0 then
          if t mod ore != 0  then 
            if t-1 mod ore != 0 then 
              orario[c,t,a] = orario[c,t+1,a] \/ orario[c,t,a] = orario[c,t-1,a] 
            else orario[c,t,a] = orario[c,t+1,a] 
            endif
          else orario[c,t,a] = orario[c,t-1,a] 
          endif
        else true
        endif
      )
    )
  )  
;

solve satisfy;

output[ 
  if j == 1 then
    if  i == 1  then 
      "\n\nAula "++show(z)++"\n m1\t" 
    else 
      if i =7 then "\n\n m"++show(i)++"\t"  else "\n m"++show(i)++"\t"  endif     
    endif
  else
    if j == ore*days+1 then "  "
    else
      if (j-1) mod ore == 0 then " " else "" endif
    endif
  endif
  ++show(orario[i,j,z])
| z in 1..n, i in 1..totInseg, j in 1..s*ore*days
];

