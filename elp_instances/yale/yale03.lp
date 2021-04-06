#const length=3.

stepless(0..length-1).

%%% Inertial fluents are fluents
fluent(F) :- inertial(F).

%%%% inertia %%%%
holds(F,S+1) :- inertial(F), stepless(S), holds(F,S),not  -holds(F,S+1).
-holds(F,S+1):- inertial(F), stepless(S),-holds(F,S),not   holds(F,S+1).

%%% non-concurrent actions
:- occurs(A,S), occurs(B,S), A!=B.

%%%% initial state: fluents false by default
-holds(F,0):-not  holds(F,0),fluent(F).

%%%%% goal  %%%%%%%
goal :- -holds(alive,length).

%%%% epistemic %%%%%%%
:- occurs(A,S), not &k{executable(A,S)}.
:- not &k{goal}.

occurs(A,S) :- not &k{ ~ occurs(A,S) }, stepless(S), action(A).

occurs(S) :- &k{occurs(A,S)}, action(A), stepless(S).
:- not occurs(S), stepless(S).

:- &k{occurs(A,S)}, &k{occurs(B,S)}, action(A), action(B), stepless(S), A!=B.


%%%% show occurs/2 %%%%
#show occurs/2.
%%%%%%%  fluents   %%%%%%%%%
inertial(loaded).
inertial(alive).

%%%%%%%  actions   %%%%%%%%
action(load).
action(pull_trigger).

%%%%%%  executable  %%%%%%% 
executable(pull_trigger,T):-  stepless(T).
executable(load,T) :- -holds(loaded,T),stepless(T).

%%%%%  effects   %%%%%%%
-holds(alive,T+1):-occurs(pull_trigger,T),holds(loaded,T),stepless(T).
-holds(loaded,T+1):-occurs(pull_trigger,T),stepless(T).
holds(loaded,T+1):-occurs(load,T),stepless(T).

%%%% initial state %%%%%
holds(alive,0).
{holds(loaded,0)}.
