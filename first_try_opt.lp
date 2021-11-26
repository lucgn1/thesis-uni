%*
#script (python)

import clingo
import math

def count_ones_pref(ex):
  id_ex = int(str(ex))
  id_ex_h_arg = int((math.log(id_ex-1)//math.log(2))+1)
  return clingo.symbol.Number(id_ex_h_arg - int(str(count_zeroes(id_ex, id_ex_h_arg))))


def count_zeroes(ID_COMPL, X):

    id_c = int(str(ID_COMPL))-1
    id_a = int(str(X))
   
    help_v = 1
    jump_bits = 0
    while( help_v < id_a ):
        if (id_c % (2**help_v)) == 0 :
          jump_bits = jump_bits + 1
        else:
          id_c = id_c - 2**(help_v-1)
        
        help_v = help_v + 1
      
    return clingo.symbol.Number(jump_bits)
  


#end.
*%


%---------------------------------------------------------------------------------------------INPUT

% all index incrementions of in groups of the compounds of the CAF ( attacks and arguments) must keep following order: FIX<UNCERTAIN<CONTROL. 
% the indexes of the uncertain attacks must keep the order: UNCERTAIN EXISTANCE < UNCERTAIN DIRECTION


%----------------------------------------------------------------------------instance of CAF


%-----------------------------------------------------------------ARGUMENTS -> (ID)


%------------------------------------------------------fix arguments 

fix_arg(1..4).


{control_arg(8)}.

%------------------------------------------------------uncertain arguments 

uncertain_arg(5..7).

first_unc_arg(FIRST) :- FIRST=#min{ X : uncertain_arg(X) }.
last_unc_arg(LAST) :- LAST=#max{ X : uncertain_arg(X) }.

%------------------------------------------------------attacks 
att_fix(1,1,3).
att_fix(2,2,1).
att_fix(3,3,7).
att_fix(4,4,3).
att_fix(5,5,4).
att_fix(6,6,3).


unc_ex_att(7,5,1).
unc_ex_att(8,6,4).

unc_dir_att(9,5,7). 

%unc_dir_att(11,6,7). 



control_att(11,8,4).


target_arg(2).


%unc_att(ATT_ID,X,Y) :- unc_ex_att(ATT_ID,X,Y).
unc_ex_att(ATT_ID,X,Y) :- unc_dir_att(ATT_ID,X,Y).		%splitting unknow direction attacks in two
unc_ex_att(ATT_ID+1,Y,X) :- unc_dir_att(ATT_ID,X,Y).

first_un_ex_att(FIRST) :- FIRST=#min{ ATT_ID : unc_ex_att(ATT_ID,_,_) }.
%*
first_un_dir_att(FIRST) :- FIRST=#min{ ATT_ID : unc_dir_att(ATT_ID,_,_) }.

att(ATT_ID,X,Y) :- att_fix(ATT_ID,X,Y).
att(ATT_ID,X,Y) :- unc_att(ATT_ID,X,Y).
att(ATT_ID,X,Y) :- control_att(ATT_ID,X,Y).
*%

set_arg_cpl(1..2**N) :- N = #count { A : uncertain_arg(A)}. %possible argument sets for a completion 

%fix and control arguments are going to be part of all completions

arg_compl(ID,1,X) :- set_arg_cpl(ID), fix_arg(X).
arg_compl(ID,1,X) :- set_arg_cpl(ID), control_arg(X).

arg_compl(ID,IN,X) :- set_arg_cpl(ID), uncertain_arg(X), first_unc_arg(FIRST), IN=(((ID-1)/(2**(X-FIRST))))\2. %leere instanz



sets_atts(1..O) :-  N = #count { ID,A,B : unc_ex_att(ID,A,B)}, O=2**N. 	% possible attack sets for a completion


%fix and control attacks are going to be part of all completions (*if their belonging arguments are part of the completion which is ensured up on using the semantics below in the program)

%sets_atts_candidate(ID,1,ATT_ID) :- sets_atts(ID), att_fix(ATT_ID,X,Y).
%sets_atts_candidate(ID,1,ATT_ID) :- sets_atts(ID), control_att(ATT_ID,X,Y), control_arg(X).
%sets_atts_candidate(ID,1,ATT_ID) :- sets_atts(ID), control_att(ATT_ID,X,Y), control_arg(Y).


%number_of_unc_ex_att(N) :- N = #count { ID,A,B : unc_ex_att(ID,A,B)}.
unc_atts_compl(SET_ID,IN,X,Y) :- sets_atts(SET_ID), unc_ex_att(ATT_ID,X,Y), first_un_ex_att(FIRST), IN=(((SET_ID-1)/(2**(ATT_ID-FIRST))))\2. %starting through generating participationvector of first uncertain attack

%unc_atts_compl(SET_ID,X,Y) :- sets_atts(SET_ID), unc_dir_att(ATT_ID,X,Y), first_un_dir_att(FIRST), IN=|(((SET_ID-1)/((3**((ATT_ID-FIRST)/2))*(2**(N_unc_ex))))\3)-1|, number_of_unc_ex_att(N_unc_ex), IN==1. %starting through generating participationvector of first uncertain attack
%unc_atts_compl(SET_ID,Y,X) :- sets_atts(SET_ID), unc_dir_att(ATT_ID,X,Y), first_un_dir_att(FIRST), IN=|((((SET_ID-1)/((3**((ATT_ID-FIRST)/2))*(2**(N_unc_ex))))+1)\3)-1|, number_of_unc_ex_att(N_unc_ex), IN==1. %starting through generating participationvector of first uncertain attack










impossible_completion(ID_COMPL,SET_ID) :- unc_atts_compl(SET_ID,0,Y,X), unc_atts_compl(SET_ID,0,X,Y), unc_dir_att(ATT_ID,X,Y), arg_compl(ID_COMPL,1,X), arg_compl(ID_COMPL,1,Y).
impossible_completion(ID_COMPL,SET_ID) :- unc_atts_compl(SET_ID,1,X,Y), unc_ex_att(ATT_ID,X,Y), arg_compl(ID_COMPL,0,X).
impossible_completion(ID_COMPL,SET_ID) :- unc_atts_compl(SET_ID,1,X,Y), unc_ex_att(ATT_ID,X,Y), arg_compl(ID_COMPL,0,Y).

completion(ID_COMPL,SET_ID_ATT) :- sets_atts(SET_ID_ATT), set_arg_cpl(ID_COMPL), not impossible_completion(ID_COMPL,SET_ID_ATT).
%completion(ID_COMPL,0) :- set_arg_cpl(ID_COMPL), unc_dir_att(ID_ATT,X,Y).
%completion(ID_COMPL,1) :- set_arg_cpl(ID_COMPL), not unc_dir_att(_,_,_).

att_compl(ID_COMPL,SET_ID_ATT,X,Y) :- completion(ID_COMPL,SET_ID_ATT), unc_atts_compl(SET_ID_ATT,1,X,Y), arg_compl(ID_COMPL,1,X), arg_compl(ID_COMPL,1,Y). 
att_compl(ID_COMPL,SET_ID_ATT,X,Y) :- completion(ID_COMPL,SET_ID_ATT), att_fix(ATT_ID,X,Y), arg_compl(ID_COMPL,1,X), arg_compl(ID_COMPL,1,Y). 
att_compl(ID_COMPL,SET_ID_ATT,X,Y) :- completion(ID_COMPL,SET_ID_ATT), control_att(ATT_ID,X,Y), arg_compl(ID_COMPL,1,X), arg_compl(ID_COMPL,1,Y). 

%number_completion(N) :-  N= #count { ID_COMPL,SET_ID_ATT : completion(ID_COMPL,SET_ID_ATT)}.
%#show number_completion/1.
%*
number_impossible_completion(N) :-  N= #count { ID_COMPL,SET_ID_ATT : impossible_completion(ID_COMPL,SET_ID_ATT)}.
#show number_impossible_completion/1.
number_unc_atts_compl(N) :-  N= #count { SET_ID,IN,X,Y : unc_atts_compl(SET_ID,IN,X,Y)}.
#show number_unc_atts_compl/1.
*%

%#show number_extension/1.
%missing_extensions(ID_COMPL) :-  N= #count { ID_EXT,X : ext_arg(ID_EXT,ID_COMPL,X)}, set_arg_cpl(ID_COMPL),  M= #count { Y : arg_compl(ID_COMPL,1,Y)}, (M*(2**M))/2!=N.
%#show missing_extensions/1.
%number_extension_ID(N) :-  N= #count { ID_EXT,ID_COMPL,X : ext_arg(ID_EXT,ID_COMPL,X)}.
%#show number_extension_ID/1.
%#show arg_compl/3.
%#show impossible_completion/2.

%completion_to_show(9).
%completion_to_show_unc_arg(ID_COMPL,SET_ID_ATT,X) :- completion_to_show(ID_COMPL), completion(ID_COMPL,SET_ID_ATT), arg_compl(ID_COMPL,1,X), uncertain_arg(X).
%completion_to_show_unc_atts(ID_COMPL,SET_ID_ATT,X,Y) :- completion_to_show(ID_COMPL), completion(ID_COMPL,SET_ID_ATT), unc_atts_compl(SET_ID_ATT,1,X,Y).
%#show completion_to_show_unc_atts/4.
%#show completion_to_show_unc_arg/3.
%unc_atts_to_show(IN,Y,X) :- unc_atts_compl(1,IN,Y,X).
%#show unc_atts_to_show/3.






%extensions
extension(1..2**N,ID) :- N = #count { X : arg_compl(ID,1,X)}, set_arg_cpl(ID). %possible argument sets for a completion 

ext_arg(ID_EXT,ID_COMPL,X) :- extension(ID_EXT,ID_COMPL), fix_arg(X), arg_compl(ID_COMPL,1,X), IN=(((ID_EXT-1)/(2**(X-1))))\2, IN==1.
ext_arg(ID_EXT,ID_COMPL,X) :- extension(ID_EXT,ID_COMPL), uncertain_arg(X), first_unc_arg(FIRST), arg_compl(ID_COMPL,1,X), IN=(((ID_EXT-1)/(2**(X-@count_zeroes(ID_COMPL, X-FIRST+1)-1))))\2, IN==1.

last_uncertain_arg(LAST_UNC) :- LAST_UNC=#max{ X : uncertain_arg(X) }.
ext_arg(ID_EXT,ID_COMPL,X) :- extension(ID_EXT,ID_COMPL), control_arg(X), first_unc_arg(FIRST), last_uncertain_arg(LAST_UNC), arg_compl(ID_COMPL,1,X), IN=(((ID_EXT-1)/(2**(X-@count_zeroes(ID_COMPL, LAST_UNC-FIRST+2)-1))))\2, IN==1.%leere instanz
%show_extensions(ID_EXT,X) :- ext_arg(ID_EXT,2,X).
%#show show_extensions/2.


%chaining sematiccriteriums can improve runtime. the more complitions are filtered out the faster!
%conflictfree
conflict(ID_COMPL,SET_ID_ATT,ID_EXT):- ext_arg(ID_EXT,ID_COMPL,X),ext_arg(ID_EXT,ID_COMPL,Y),att_compl(ID_COMPL,SET_ID_ATT,X,Y).
conflict_free(ID_COMPL,SET_ID_ATT,ID_EXT) :- completion(ID_COMPL,SET_ID_ATT), not conflict(ID_COMPL,SET_ID_ATT,ID_EXT), extension(ID_EXT,ID_COMPL).

%admissible
defeated_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,Y) :- conflict_free(ID_COMPL,SET_ID_ATT,ID_EXT), ext_arg(ID_EXT,ID_COMPL,X),arg_compl(ID_COMPL,1,Y), att_compl(ID_COMPL,SET_ID_ATT,X,Y).
not_admissible(ID_COMPL,SET_ID_ATT,ID_EXT):- conflict_free(ID_COMPL,SET_ID_ATT,ID_EXT), ext_arg(ID_EXT,ID_COMPL,Y), arg_compl(ID_COMPL,1,X), att_compl(ID_COMPL,SET_ID_ATT,X,Y), not defeated_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,X).
admissible(ID_COMPL,SET_ID_ATT,ID_EXT) :- conflict_free(ID_COMPL,SET_ID_ATT,ID_EXT), not not_admissible(ID_COMPL,SET_ID_ATT,ID_EXT).




%complete
not_defended_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,Y) :- admissible(ID_COMPL,SET_ID_ATT,ID_EXT), extension(ID_EXT,ID_COMPL), arg_compl(ID_COMPL,1,X), arg_compl(ID_COMPL,1,Y), att_compl(ID_COMPL,SET_ID_ATT,X,Y), not defeated_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,X).
not_complete(ID_COMPL,SET_ID_ATT,ID_EXT):- admissible(ID_COMPL,SET_ID_ATT,ID_EXT), arg_compl(ID_COMPL,1,X), not ext_arg(ID_EXT,ID_COMPL,X), not not_defended_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,X), not defeated_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,X).
complete(ID_COMPL,SET_ID_ATT,ID_EXT) :- admissible(ID_COMPL,SET_ID_ATT,ID_EXT), not not_complete(ID_COMPL,SET_ID_ATT,ID_EXT).



%stable
%not_stable(ID_COMPL,SET_ID_ATT,ID_EXT):- admissible(ID_COMPL,SET_ID_ATT,ID_EXT), arg_compl(ID_COMPL,1,X), not ext_arg(ID_EXT,ID_COMPL,X), not defeated_by_extension(ID_COMPL,SET_ID_ATT,ID_EXT,X).
%stable(ID_COMPL,SET_ID_ATT,ID_EXT) :- admissible(ID_COMPL,SET_ID_ATT,ID_EXT), not not_stable(ID_COMPL,SET_ID_ATT,ID_EXT).

%grounded
%not_grounded(ID_COMPL,SET_ID_ATT,ID_EXT_1) :- complete(ID_COMPL,SET_ID_ATT,ID_EXT_1), complete(ID_COMPL,SET_ID_ATT,ID_EXT_2), ID_EXT_1>ID_EXT_2.
%grounded(ID_COMPL,SET_ID_ATT,ID_EXT) :- complete(ID_COMPL,SET_ID_ATT,ID_EXT), not not_grounded(ID_COMPL,SET_ID_ATT,ID_EXT).

%preffered
%a preffered challenger of a extension must have more 1s in the binary representation of its id-1 than the challenged extension
%preffered_challenged(ID_COMPL,SET_ID_ATT,ID_EXT_2,ID_EXT_1) :- complete(ID_COMPL,SET_ID_ATT,ID_EXT_2), complete(ID_COMPL,SET_ID_ATT,ID_EXT_1), @count_ones_pref(ID_EXT_2)>@count_ones_pref(ID_EXT_1), ID_EXT_2>ID_EXT_1.
%preffered_challenge_defended(ID_COMPL,SET_ID_ATT,ID_EXT_2,ID_EXT_1) :- preffered_challenged(ID_COMPL,SET_ID_ATT,ID_EXT_2,ID_EXT_1), ext_arg(ID_EXT_1,ID_COMPL,X), not ext_arg(ID_EXT_2,ID_COMPL,X).
%not_preffered(ID_COMPL,SET_ID_ATT,ID_EXT_1):- complete(ID_COMPL,SET_ID_ATT,ID_EXT_1), preffered_challenged(ID_COMPL,SET_ID_ATT,ID_EXT_2,ID_EXT_1), not preffered_challenge_defended(ID_COMPL,SET_ID_ATT,ID_EXT_2,ID_EXT_1).
%preffered(ID_COMPL,SET_ID_ATT,ID_EXT):- complete(ID_COMPL,SET_ID_ATT,ID_EXT), not not_preffered(ID_COMPL,SET_ID_ATT,ID_EXT).

%number_preffered_challenged(N) :-  N= #count { ID_COMPL,SET_ID_ATT,ID_EXT_1,ID_EXT_2 : preffered_challenge_defended(ID_COMPL,SET_ID_ATT,ID_EXT_1,ID_EXT_2)}.
%#show number_preffered_challenged/1.
%#show preffered_challenge_defended/4.

#show.
%number_complete(N) :-  N= #count { ID_COMPL,SET_ID_ATT,ID_EXT : complete(ID_COMPL,SET_ID_ATT,ID_EXT)}.
%#show number_complete/1.
%*
number_extension_arg(N) :-  N= #count { ID_EXT,ID_COMPL,X : ext_arg(ID_EXT,ID_COMPL,X)}.
#show number_extension_arg/1.
number_extension(N) :-  N= #count { ID_EXT,ID_COMPL : extension(ID_EXT,ID_COMPL)}.
#show number_extension/1.
number_compl(N) :-  N= #count { ID : set_arg_cpl(ID)}.
#show number_compl/1.
number_completion(N) :-  N= #count { ID_COMPL,SET_ID_ATT : completion(ID_COMPL,SET_ID_ATT)}.
#show number_completion/1.
ext_arg_control(ID_EXT,ID_COMPL,X) :- ext_arg(ID_EXT,ID_COMPL,X), control_arg(X).
number_ext_arg_control(N) :-  N= #count { ID_EXT,ID_COMPL,X : ext_arg_control(ID_EXT,ID_COMPL,X)}.
#show number_ext_arg_control/1.
%#show att_compl/4.
number_att_compl(N) :-  N= #count { ID_COMPL,SET_ID_ATT,X,Y : att_compl(ID_COMPL,SET_ID_ATT,X,Y)}.
#show number_att_compl/1.
#show unc_ex_att/3.
*%

%credulous
%target_semantic_Ext(ID_COMPL,SET_ID_ATT,ID_EXT) :- preffered(ID_COMPL,SET_ID_ATT,ID_EXT).
%ext_missing_target(ID_COMPL,SET_ID_ATT,ID_EXT) :- target_arg(X), target_semantic_Ext(ID_COMPL,SET_ID_ATT,ID_EXT), not ext_arg(ID_EXT,ID_COMPL,X).
%controllable_completion(ID_COMPL,SET_ID_ATT) :- target_semantic_Ext(ID_COMPL,SET_ID_ATT,ID_EXT), not ext_missing_target(ID_COMPL,SET_ID_ATT,ID_EXT).
%uncontrollable() :- completion(ID_COMPL,SET_ID_ATT), not controllable_completion(ID_COMPL,SET_ID_ATT).
%:- uncontrollable().

%#show controllable_completion/2.


%skeptical
target_semantic_Ext(ID_COMPL,SET_ID_ATT,ID_EXT) :- complete(ID_COMPL,SET_ID_ATT,ID_EXT).
ext_missing_target(ID_COMPL,SET_ID_ATT,ID_EXT) :- target_arg(X), target_semantic_Ext(ID_COMPL,SET_ID_ATT,ID_EXT), not ext_arg(ID_EXT,ID_COMPL,X).
uncontrollable() :- ext_missing_target(ID_COMPL,SET_ID_ATT,ID_EXT).
:- uncontrollable().


