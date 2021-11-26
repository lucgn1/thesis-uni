%#program base.
%*
control_arg(8).

control_att(8,4).



fix_arg(1..4).



uncertain_arg(5..7).
%first_unc_arg(FIRST) :- FIRST=#min{ X : uncertain_arg(X) }.
%last_unc_arg(LAST) :- LAST=#max{ X : uncertain_arg(X) }.


att_fix(1,3).
att_fix(2,1).
att_fix(3,7).
att_fix(4,3).
att_fix(5,4).
att_fix(6,3).


unc_ex_att(5,1).
unc_ex_att(6,4).
%first_un_ex_att(FIRST) :- FIRST=#min{ ATT_ID : unc_ex_att(ATT_ID,_,_) }.
%last_un_ex_att(LAST) :- LAST=#max{ ATT_ID : unc_ex_att(ATT_ID,_,_) }.

unc_dir_att(5,7). 
%first_unc_dir_arg(FIRST) :- FIRST=#min{ ATT_ID : unc_dir_att(ATT_ID,_,_) }.
%last_unc_dir_arg(LAST) :- LAST=#max{ ATT_ID : unc_dir_att(ATT_ID,_,_) }.


target_arg(2).

%highest_id_completion(2**(LAST_ARG - FIRST_ARG + 1), 2**(LAST_UN_EX_ATT - FIRST_UN_EX_ATT + 1) * 3**(LAST_UN_DIR_ATT - FIRST_UN_DIR_ATT + 1)) :- last_unc_arg(LAST_ARG), first_unc_arg(FIRST_ARG), first_un_ex_att(FIRST_UN_EX_ATT), last_un_ex_att(LAST_UN_EX_ATT), first_unc_dir_arg(FIRST_UN_DIR_ATT), last_unc_dir_arg(LAST_UN_DIR_ATT).

*%


{completion_arg(X)} :- control_arg(X).

#program completion.

completion_arg(X) :- fix_arg(X).
{completion_arg(X)} :- uncertain_arg(X).

 

completion_att(X,Y):- att_fix(X,Y), completion_arg(X), completion_arg(Y).
{completion_att(X,Y)}:- unc_ex_att(X,Y), completion_arg(X), completion_arg(Y).
{completion_att(X,Y)} :- unc_dir_att(X,Y), completion_arg(X), completion_arg(Y).
{completion_att(Y,X)} :- unc_dir_att(X,Y), completion_att(X,Y), completion_arg(X), completion_arg(Y).
completion_att(Y,X) :- unc_dir_att(X,Y), not completion_att(X,Y), completion_arg(X), completion_arg(Y).
completion_att(X,Y):- control_att(X,Y), completion_arg(X), completion_arg(Y).

#show completion_arg/1.
#show completion_att/3.

#program extension.

{extension_arg(X)} :- completion_arg(X).



%extension info
%id_ex(ID_SET + 1) :- ID_SET = #sum{ 2**(X-1) : extension_arg(X)}.
%extension_info(ID_COMPL_ARG + 1,ID_UNC_ATT + ID_UNC_DIR_1_ATT + ID_UNC_DIR_2_ATT + 1,ID_EX,A) :- ID_COMPL_ARG= #sum{ 2**(X-FIRST) : completion_arg(X),uncertain_arg(X),first_unc_arg(FIRST)}, ID_UNC_ATT= #sum{ 2**(ID-FIRST) : completion_att(ID,X,Y), unc_ex_att(ID,X,Y), first_un_ex_att(FIRST)}, ID_UNC_DIR_1_ATT= #sum{ 2**(ID-FIRST) : completion_att(ID,X,Y), unc_dir_att(ID,X,Y), first_un_ex_att(FIRST)}, ID_UNC_DIR_2_ATT= #sum{ 2**(ID+1-FIRST) : completion_att(ID+1,Y,X), unc_dir_att(ID,X,Y), first_un_ex_att(FIRST)}, id_ex(ID_EX), target_args_missing(A).
#show extension_arg/1.


#program skeptical.

target_args_missing():- target_arg(X), not extension_arg(X).
:- not target_args_missing().

#program credulous.

:- target_arg(X), not extension_arg(X).


#program filter_conflict_free.
%conflictfree
:- extension_arg(X), extension_arg(Y), completion_att(X,Y).

#program filter_admissible.
%conflictfree
:- extension_arg(X), extension_arg(Y), completion_att(X,Y).
%admissible
defeated_by_extension(Y) :- extension_arg(X), completion_arg(Y), completion_att(X,Y).
:- completion_arg(X), extension_arg(Y), completion_att(X,Y), not defeated_by_extension(X).

#program filter_complete.
%conflictfree
:- extension_arg(X), extension_arg(Y), completion_att(X,Y).
%admissible
defeated_by_extension(Y) :- extension_arg(X), completion_arg(Y), completion_att(X,Y).
:- completion_arg(X), extension_arg(Y), completion_att(X,Y), not defeated_by_extension(X).
%complete
not_defended_by_extension(Y) :- completion_arg(X), completion_arg(Y), completion_att(X,Y), not defeated_by_extension(X).
:- completion_arg(X), not extension_arg(X), not not_defended_by_extension(X), not defeated_by_extension(X).

#show extension_arg/1.

#program filter_stable.
%conflictfree
:- extension_arg(X), extension_arg(Y), completion_att(X,Y).
%admissible
defeated_by_extension(Y) :- extension_arg(X), completion_arg(Y), completion_att(X,Y).
:- completion_arg(X), extension_arg(Y), completion_att(X,Y), not defeated_by_extension(X).
%stable
:- completion_arg(X), not extension_arg(X), not defeated_by_extension(X).



%after gathering part




#program filter_grounded.
%grounded
grounded_ext(ID_COMPL_ARG,ID_UNC,ID_EX_1,A) :- id_ex(ID_EX_2), extension_info(ID_COMPL_ARG,ID_UNC,ID_EX_1,A), not extension_info(ID_COMPL_ARG,ID_UNC,ID_EX_2,_), ID_EX_1>ID_EX_2.

#program filter_preferred.
%preferred
%*
#script (python)

#import clingo
import math

def is_included(ex_1, ex_2):
    id_ex_1 = int(str(ex_1))
    id_ex_2 = int(str(ex_2))

    if id_ex_1 > 1:
        first_bit = (math.log(id_ex_1-1)//math.log(2))+1
    else:
        return 1
    

    id_diff = id_ex_2 - id_ex_1

    help_v = 1
    while( help_v <= first_bit ):

        if (id_diff % (2**help_v)) != 0 :
            return 0
        help_v = help_v + 1
    
    return 1
 


#end.
*%
not_preferred_ext(ID_COMPL_ARG,ID_UNC,ID_EX_1,A) :- extension_info(ID_COMPL_ARG,ID_UNC,ID_EX_1,A), extension_info(ID_COMPL_ARG,ID_UNC,ID_EX_2,_), ID_EX_1<ID_EX_2, @is_included(ID_EX_1,ID_EX_2)==1.
preferred_ext(ID_COMPL_ARG,ID_UNC,ID_EX_1,A) :- extension_info(ID_COMPL_ARG,ID_UNC,ID_EX_1,A), not not_preferred_ext(ID_COMPL_ARG,ID_UNC,ID_EX_1,A).




#program credulous_controllability.
completion(ID_ARG_SET,ID_ATT_SET) :- highest_id_completion(COMPL_ARGS, UNC_ATTS), ID_ARG_SET=1..COMPL_ARGS, ID_ATT_SET=1..UNC_ATTS.
credulous_completion(ID_COMPL_ARG,ID_UNC) :- extension_info(ID_COMPL_ARG,ID_UNC,ID_EX,0).
not_credulous_controllable() :- completion(ID_ARG_SET,ID_ATT_SET), not credulous_completion(ID_ARG_SET,ID_ATT_SET).
:- not not_credulous_controllable().

#program credulous_controllability_grounded.
completion(ID_ARG_SET,ID_ATT_SET) :- highest_id_completion(COMPL_ARGS, UNC_ATTS), ID_ARG_SET=1..COMPL_ARGS, ID_ATT_SET=1..UNC_ATTS.
credulous_completion(ID_COMPL_ARG,ID_UNC) :- grounded_ext(ID_COMPL_ARG,ID_UNC,ID_EX,0).
not_credulous_controllable() :- completion(ID_ARG_SET,ID_ATT_SET), not credulous_completion(ID_ARG_SET,ID_ATT_SET).
:- not not_credulous_controllable().

#program credulous_controllability_preferred.
completion(ID_ARG_SET,ID_ATT_SET) :- highest_id_completion(COMPL_ARGS, UNC_ATTS), ID_ARG_SET=1..COMPL_ARGS, ID_ATT_SET=1..UNC_ATTS.
credulous_completion(ID_COMPL_ARG,ID_UNC) :- preferred_ext(ID_COMPL_ARG,ID_UNC,ID_EX,0).
not_credulous_controllable() :- completion(ID_ARG_SET,ID_ATT_SET), not credulous_completion(ID_ARG_SET,ID_ATT_SET).
:- not not_credulous_controllable().

#program skeptical_controllability_grounded.
:- grounded_ext(ID_COMPL_ARG,ID_UNC,ID_EX,1).

#program skeptical_controllability_preferred.
:- preferred_ext(ID_COMPL_ARG,ID_UNC,ID_EX,1).

#program skeptical_controllability.
:- extension_info(ID_COMPL_ARG,ID_UNC,ID_EX,1).



#program extension_test.

{extension_arg(X)} :- completion_arg(X).

:- target_arg(X), not extension_arg(X).