
%---------------------------------------------------------------------------------------------INPUT

% all index incrementions of in groups of the compounds of the CAF ( attacks and arguments) must keep following order: FIX<UNCERTAIN<CONTROL. 
% the indexes of the uncertain attacks must keep the order: UNCERTAIN EXISTANCE < UNCERTAIN DIRECTION


%----------------------------------------------------------------------------instance of CAF

target_arg(2).
%-----------------------------------------------------------------ARGUMENTS -> (ID)


%------------------------------------------------------fix arguments 

fix_arg(1..4).


%------------------------------------------------------uncertain arguments 

uncertain_arg(5..7).


%-------------------------------------------------index of uncertain arguments


first_unc_arg(5).
last_unc_arg(7).


%------------------------------------------------------control arguments 

{ control_arg(8) }.



%-----------------------------------------------------------------ATTACKS -> (ID,Attacker,Attacked)


%------------------------------------------------------fix attacks 

att_fix(1,1,3).
att_fix(2,2,1).
att_fix(3,3,7).
att_fix(4,4,3).
att_fix(5,5,4).
att_fix(6,6,3).


%------------------------------------------------------uncertain attacks

%-------------------------uncertain existance

unc_ex_att(7,5,1).
unc_ex_att(8,6,4).


%-------------------------uncertain direction

%each one gets an ID equals ot its succesor uncertain direction attack incremented by two in the process, because it is project as two uncertain existance attacks. 
%Exception: the first one gets the ID of the uncertain existance succesor plus 1.

unc_dir_att(9,5,7). 



%-------------------------index of uncertain attacks

first_unc_att(7).
last_unc_att(10). %last unc ID plus number of unc_dir args



%------------------------------------------------------control attacks

control_att(11,8,4).


%---------------------------------------------------------------------------------------PROBLEM INPUT


%----------------------target arguments -> target_arg(ID)

%target_arg(2).




%-----------------------kind of problem: 
%*
shows the answer of the examined problem. If the problem to be examined is the skeptical controllability one, then the credulous_controllable lines should be commented and 
the skeptical one decommented, as their corresponding code parts on the bottom of the programm 
*% 

%#show credulous_controllable/0.
%#show not_credulous_controllable/0.


%#show skeptical_controllable/0.
%#show not_skeptical_controllable/0.



#program notbase.
%-------------------------------------------------------------------------------PROJECTION OF THE SEARCH SPACE


%*
this part of the program is splitted in three major parts. The projection of all possible argument sets of a completion, the projection of all possible attack sets of a completion and
the projection of all possible argument sets with the arguments of a completion which represents all possible extensions. The used approach on all 3 parts is always the same: to build
matrixes that can represent each of the possible combinations.
*%


% COMPLETION ARGUMENTMATRIX

%arguments are represented through the pradicate att_compl(ID,A,X) -> ID is the ID of its belonging argument set on the matrix, A shows if the argument is part of the set represented 
%by the ID, and X shows which CAF argument this argument belongs to

set_arg_cpl(1..2**N) :- N = #count { A : uncertain_arg(A)}. %possible argument sets for a completion 

%fix and control arguments are going to be part of all completions

arg_compl(ID,1,X) :- set_arg_cpl(ID), fix_arg(X).
arg_compl(ID,1,X) :- set_arg_cpl(ID), control_arg(X).

arg_compl(1,0,X) :- set_arg_cpl(1), uncertain_arg(X). %leere instanz
arg_compl(ID,0,FIRST) :- set_arg_cpl(ID), ID!=1, arg_compl(ID-1,1,FIRST), first_unc_arg(FIRST). %starting through generating participationvector of first uncertain argument
arg_compl(ID,1,FIRST) :- set_arg_cpl(ID), ID!=1, arg_compl(ID-1,0,FIRST), first_unc_arg(FIRST). 

%the vector of the other members are built through looking up the stance of the predecessor argument and its own previous stance.

arg_compl(ID,A,X) :- set_arg_cpl(ID), uncertain_arg(X), arg_compl(ID-1,A,X), arg_compl(ID,B,X-1), arg_compl(ID-1,B,X-1), ID>1, first_unc_arg(FIRST), X>FIRST, last_unc_arg(LAST), X<=LAST, A=(0;1), B=(0;1). %generating participationvectors of the other arguments
arg_compl(ID,A,X) :- set_arg_cpl(ID), uncertain_arg(X), arg_compl(ID-1,A,X), arg_compl(ID,1,X-1), arg_compl(ID-1,0,X-1), ID>1, first_unc_arg(FIRST), X>FIRST, last_unc_arg(LAST), X<=LAST, A=(0;1).

arg_compl(ID,A,X) :- set_arg_cpl(ID), uncertain_arg(X), arg_compl(ID-1,B,X), arg_compl(ID,0,X-1), arg_compl(ID-1,1,X-1), ID>1, first_unc_arg(FIRST), X>FIRST, last_unc_arg(LAST), X<=LAST, A=(0;1), B=(0;1), A!=B.




% COMPLETION ATTACKSMATRIX

%attacks are represented through the pradicate att_compl(ID,A,ATT_ID) -> ID is the ID of its belonging attack set on the matrix, A shows if the attack is part of the set represented 
%by the ID, and ATT_ID shows which CAF attack this attack belongs to

sets_unc_atts(1..O*P) :- M = #count { ID,C,D : unc_dir_att(ID,C,D)}, N = #count { ID,A,B : unc_ex_att(ID,A,B)}, O=2**N, P=3**M. 	% possible attack sets for a completion


%fix and control attacks are going to be part of all completions (*if their belonging arguments are part of the completion which is ensured up on using the semantics below in the program)

att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), att_fix(ATT_ID,X,Y).
att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), control_att(ATT_ID,X,Y), control_arg(X).
att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), control_att(ATT_ID,X,Y), control_arg(Y).

first_unc_dir_att(ATT_ID,X,Y) :- unc_dir_att(ATT_ID,X,Y).		%splitting unknow direction attacks in two
second_unc_dir_att(ATT_ID+1,Y,X) :- unc_dir_att(ATT_ID,X,Y).


att_compl(1,0,ATT_ID) :- sets_unc_atts(1), unc_ex_att(ATT_ID,X,Y). %leere instanz
att_compl(1,1,ATT_ID) :- sets_unc_atts(1), first_unc_dir_att(ATT_ID,X,Y). %leere instanz
att_compl(1,0,ATT_ID) :- sets_unc_atts(1), second_unc_dir_att(ATT_ID,X,Y). %leere instanz


att_compl(ID,0,FIRST) :- sets_unc_atts(ID), ID!=1, att_compl(ID-1,1,FIRST), first_unc_att(FIRST), unc_ex_att(ATT_ID,X,Y). %starting through generating participationvector of first uncertain attack
att_compl(ID,1,FIRST) :- sets_unc_atts(ID), ID!=1, att_compl(ID-1,0,FIRST), first_unc_att(FIRST), unc_ex_att(ATT_ID,X,Y). 


%the vector of the other members are built through looking up the stance of the predecessor attack and its own previous stance. additional looking up of the successor is needed for the calculation of the participation 
%of members of an uncertain direction attack 

%rules for uncertain existance attacks
att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), unc_ex_att(ATT_ID,X,Y), att_compl(ID-1,A,ATT_ID), att_compl(ID,B,ATT_ID-1), att_compl(ID-1,B,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1), B=(0;1). 				%existance of uncertain attacks
att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), unc_ex_att(ATT_ID,X,Y), att_compl(ID-1,A,ATT_ID), att_compl(ID,1,ATT_ID-1), att_compl(ID-1,0,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1).

att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), unc_ex_att(ATT_ID,X,Y), att_compl(ID-1,B,ATT_ID), att_compl(ID,0,ATT_ID-1), att_compl(ID-1,1,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1), B=(0;1), A!=B.


%rules for uncertain direction attacks
att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), first_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,A,ATT_ID), att_compl(ID,B,ATT_ID-1), att_compl(ID-1,B,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1), B=(0;1). 			%first direction (direction unknown)
att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), first_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,A,ATT_ID), att_compl(ID,1,ATT_ID-1), att_compl(ID-1,0,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1).

att_compl(ID,0,ATT_ID) :- sets_unc_atts(ID), first_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,1,ATT_ID), att_compl(ID,0,ATT_ID-1), att_compl(ID-1,1,ATT_ID-1), att_compl(ID-1,0,ATT_ID+1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST.
att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), first_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,0,ATT_ID), att_compl(ID,0,ATT_ID-1), att_compl(ID-1,1,ATT_ID-1), att_compl(ID-1,1,ATT_ID+1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST.



att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), second_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,1,ATT_ID), att_compl(ID,0,ATT_ID-1), att_compl(ID-1,0,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST. 			%second direction (direction unknown)
att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), second_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,1,ATT_ID), att_compl(ID,1,ATT_ID-1), att_compl(ID-1,0,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST.

att_compl(ID,1,ATT_ID) :- sets_unc_atts(ID), second_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,0,ATT_ID), att_compl(ID,0,ATT_ID-1), att_compl(ID-1,1,ATT_ID-1), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST.
att_compl(ID,0,ATT_ID) :- sets_unc_atts(ID), second_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,1,ATT_ID), att_compl(ID-1,1,ATT_ID-1), att_compl(ID-2,1,ATT_ID-1), att_compl(ID,0,ATT_ID-2), att_compl(ID-1,1,ATT_ID-2), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST.
att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), second_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,A,ATT_ID), att_compl(ID,1,ATT_ID-1), att_compl(ID,B,ATT_ID-2), att_compl(ID-1,B,ATT_ID-2), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1), B=(0;1).
att_compl(ID,A,ATT_ID) :- sets_unc_atts(ID), second_unc_dir_att(ATT_ID,X,Y), att_compl(ID-1,A,ATT_ID), att_compl(ID,1,ATT_ID-1), att_compl(ID,1,ATT_ID-2), att_compl(ID-1,0,ATT_ID-2), ID>1, first_unc_att(FIRST), ATT_ID>FIRST, last_unc_att(LAST), ATT_ID<=LAST, A=(0;1).






% EXTENSIONSMATRIXES

%finding neighbour for arg_compl
%this is very important because the abscence of uncertain and control arguments in a completion destroys the indexing!!!

nr_neighbour_arg_compl_(ID,X,X-1) :- arg_compl(ID,1,X), arg_compl(ID,1,X-1), X>1.
looking_for_neighbour_arg_compl(ID,X,X-1) :- arg_compl(ID,1,X), arg_compl(ID,0,X-1).
looking_for_neighbour_arg_compl(ID,Y,X-1) :- arg_compl(ID,0,X), arg_compl(ID,0,X-1), looking_for_neighbour_arg_compl(ID,Y,X).
nr_neighbour_arg_compl_(ID,Y,X-1) :- arg_compl(ID,0,X), arg_compl(ID,1,X-1), looking_for_neighbour_arg_compl(ID,Y,X).



%definiton of extensions of the completions

extension(ID,SET_ARGS_CPL_ID) :- set_arg_cpl(SET_ARGS_CPL_ID), ID=(1..2**N), N= #count { X : arg_compl(SET_ARGS_CPL_ID,1,X)}. % possible extensions in a completion

arg_ext(1,0,X,SET_ARGS_CPL_ID) :- extension(1,SET_ARGS_CPL_ID), arg_compl(SET_ARGS_CPL_ID,1,X). %leere instanz



%extensionmatrix generator


arg_ext(ID,0,1,SET_ARGS_CPL_ID) :- extension(ID,SET_ARGS_CPL_ID), ID!=1, arg_ext(ID-1,1,1,SET_ARGS_CPL_ID). %starting through generating participationvector of first argument
arg_ext(ID,1,1,SET_ARGS_CPL_ID) :- extension(ID,SET_ARGS_CPL_ID), ID!=1, arg_ext(ID-1,0,1,SET_ARGS_CPL_ID). 

%the vector of the other members are built through looking up the stance of the predecessor argument and its own previous stance

arg_ext(ID,A,X,SET_ARGS_CPL_ID) :- extension(ID,SET_ARGS_CPL_ID), arg_compl(SET_ARGS_CPL_ID,1,X), arg_ext(ID-1,A,X,SET_ARGS_CPL_ID), arg_ext(ID,B,Y,SET_ARGS_CPL_ID), arg_ext(ID-1,B,Y,SET_ARGS_CPL_ID), nr_neighbour_arg_compl_(SET_ARGS_CPL_ID,X,Y), ID>1, X>1, A=(0;1), B=(0;1). %generating participationvectors of the other arguments
arg_ext(ID,A,X,SET_ARGS_CPL_ID) :- extension(ID,SET_ARGS_CPL_ID), arg_compl(SET_ARGS_CPL_ID,1,X), arg_ext(ID-1,A,X,SET_ARGS_CPL_ID), arg_ext(ID,1,Y,SET_ARGS_CPL_ID), arg_ext(ID-1,0,Y,SET_ARGS_CPL_ID), nr_neighbour_arg_compl_(SET_ARGS_CPL_ID,X,Y), ID>1, X>1, A=(0;1).

arg_ext(ID,A,X,SET_ARGS_CPL_ID) :- extension(ID,SET_ARGS_CPL_ID), arg_compl(SET_ARGS_CPL_ID,1,X), arg_ext(ID-1,B,X,SET_ARGS_CPL_ID), arg_ext(ID,0,Y,SET_ARGS_CPL_ID), arg_ext(ID-1,1,Y,SET_ARGS_CPL_ID), nr_neighbour_arg_compl_(SET_ARGS_CPL_ID,X,Y), ID>1, X>1, A=(0;1), B=(0;1), A!=B.




% ------------------------------------------------------------------------------COMPLETION DEFINITION: 1 attack set + 1 argument set


completion(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- set_arg_cpl(SET_ARGS_CPL_ID), sets_unc_atts(SET_ATTS_CPL_ID).
completion_extensions(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- completion(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), extension(EXT_ID,SET_ARGS_CPL_ID).




%-------------------------------------------------------------------------------SEMANTICS

%helper predicates to connect all attacks for easier examination of completions

att(ATT_ID,X,Y) :- att_fix(ATT_ID,X,Y).
att(ATT_ID,X,Y) :- unc_ex_att(ATT_ID,X,Y).
att(ATT_ID,X,Y) :- first_unc_dir_att(ATT_ID,X,Y).
att(ATT_ID,X,Y) :- second_unc_dir_att(ATT_ID,X,Y).
att(ATT_ID,X,Y) :- control_att(ATT_ID,X,Y), control_arg(X).
att(ATT_ID,X,Y) :- control_att(ATT_ID,X,Y), control_arg(Y).


%conflict

conflict(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- att_compl(SET_ATTS_CPL_ID,1,ATT_ID), att(ATT_ID,X,Y), arg_ext(EXT_ID,1,X,SET_ARGS_CPL_ID), arg_ext(EXT_ID,1,Y,SET_ARGS_CPL_ID).																									


%conflict_free / first admissibility criteria -> extensions without conflicts

conflict_free(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- completion_extensions(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), not conflict(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID).																										




%defeated

defeated_by_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,Y) :- arg_ext(EXT_ID,1,X,SET_ARGS_CPL_ID), arg_ext(EXT_ID,B,Y,SET_ARGS_CPL_ID), att_compl(SET_ATTS_CPL_ID,1,ATT_ID), att(ATT_ID,X,Y).	


%second admissibility criteria: all arguments must be defended by the existansion ext so there should be no not_defended_by_arg_ext for an existasion to fulfill this criteria		
															
not_defended_by_arg_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- att_compl(SET_ATTS_CPL_ID,1,ATT_ID), att(ATT_ID,X,Y), not defeated_by_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X), arg_ext(EXT_ID,1,Y,SET_ARGS_CPL_ID), arg_ext(EXT_ID,A,X,SET_ARGS_CPL_ID).					


%admissible

admissible(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID):- not not_defended_by_arg_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), conflict_free(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID).																									




%defended by extension / third completness criteria
%werden von außenangriffen verteidigt, aber nicht von ext selbst angegriffen

defended_by_arg_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X) :- att_compl(SET_ATTS_CPL_ID,1,ATT_ID), att(ATT_ID,X,Y), defeated_by_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,Y), arg_ext(EXT_ID,B,X,SET_ARGS_CPL_ID).																
outsider_defended(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID):-  arg_ext(EXT_ID,0,X,SET_ARGS_CPL_ID), defended_by_arg_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X), not defeated_by_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X).            											


%argumente außerhalb von ext, die angegriffen werden

att_arg_out(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X) :-  arg_ext(EXT_ID,0,X,SET_ARGS_CPL_ID), att_compl(SET_ATTS_CPL_ID,1,ATT_ID), att(ATT_ID,Y,X), arg_ext(EXT_ID,(0;1),Y,SET_ARGS_CPL_ID).


%ext, die argumente die nicht angegriffen werden nicht beinhalten

unatt_arg_out_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- not att_arg_out(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X), completion_extensions(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), arg_ext(EXT_ID,0,X,SET_ARGS_CPL_ID).


%ext, die nicht angegriffene argumente beinhalten
														
not_unatt_arg_out_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- completion_extensions(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), not unatt_arg_out_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID).																						


%if all conditions are met -> the given extension is complete

complete(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- not outsider_defended(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), admissible(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), not_unatt_arg_out_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID).  





% CONTROLLABILITY




% credulous CONTROLLABILITY


%Credulous controllability -> Ziel Argument muss sich in mindestens eine extension bei allen Completions befinden

%target_arg_compl(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X) :- arg_ext(EXT_ID,1,X,SET_ARGS_CPL_ID), complete(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), target_arg(X). 							
%target_missing(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- not target_arg_compl(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X), completion(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), target_arg(X).

%Wenn es mindestens eine Completion keine Extensions besitzt, die die Kriterien der Semantik zwar erfüllen aber mindestens einer der target_arg nicht vorkommt -> not_credulous_controllable, da ->target_missing

%not_credulous_controllable() :- target_missing(SET_ARGS_CPL_ID,SET_ATTS_CPL_ID).
%credulous_controllable() :- not not_credulous_controllable().



% skeptical CONTROLLABILITY

%skeptical controllability -> Ziel Argument muss sich bei allen extensions von allen Completions befinden

target_missing(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- arg_ext(EXT_ID,0,X,SET_ARGS_CPL_ID), complete(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), target_arg(X).							
%target_missing(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID) :- not target_arg_ext(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID,X), complete(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID), target_arg(X).

%Wenn es mindestens eine Extension existiert, die die Kriterien der Semantik zwar erfüllt aber mindestens einer der target_arg nicht vorkommt -> not_skeptical_controllable, da ->target_missing

not_skeptical_controllable() :- target_missing(EXT_ID,SET_ARGS_CPL_ID,SET_ATTS_CPL_ID).
skeptical_controllable() :- not not_skeptical_controllable().


#show skeptical_controllable/0.

#show not_skeptical_controllable/0.



