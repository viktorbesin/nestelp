eligible(X) :- high(X).
eligible(X) :- minority(X), fair(X).
-eligible(X) :- -fair(X), -high(X).
interview(X) :- not &k{ eligible(X)}, not &k{ -eligible(X)}, student(X).
student(mike).
fair(mike),high(mike).