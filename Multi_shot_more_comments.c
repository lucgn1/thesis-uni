#include <clingo.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <time.h>
#include <math.h>

//All of this code got written with the examples of the clingo API of https://github.com/potassco/clingo .
/*
//used on some implememnted ASP program to help on ID calculations. the log2 function should be changed to the translation of log2 through usage of ln to spare the usage of other libraries on other platforms
int count_ones_pref(int id_ex) {
    int id_ex_h = (int)(log2(id_ex - 1)+1);
    return id_ex - count_zeroes(id_ex, id_ex_h);
}
//used on some implememnted ASP program to help on ID calculations 
int count_zeroes(int id_c, int id_a)
{
    int id_c_bits = id_c - 1;
    int help_v = 1;
    int jump_bits = 0;

    while (help_v < id_a)
    {
        if (id_c_bits % (int)pow((double)2, (double)(help_v)) == 0)
        {
            jump_bits++;
        }
        else
        {
            id_c_bits = id_c_bits - (int) pow((double) 2 , (double) (help_v - 1));
        }
        help_v++;
    }
    return jump_bits;
    
}

// inject terms via a callback. used to call/inject functions used in the ASP programm
bool ground_callback(clingo_location_t const *location, char const *name, clingo_symbol_t const *arguments, size_t arguments_size, void *data, clingo_symbol_callback_t symbol_callback, void *symbol_callback_data) {
   if (strcmp(name, "count_ones_pref") == 0 && arguments_size == 1) {
    int id_ex;
    clingo_symbol_t sym;

    clingo_symbol_number(arguments[0], &id_ex);
     
     clingo_symbol_create_number(count_ones_pref(id_ex), &sym);
     return symbol_callback(&sym, 1, symbol_callback_data);
   }
   if (strcmp(name, "count_zeroes") == 0 && arguments_size == 2) {
       int id_c;
       int id_a;
       clingo_symbol_t sym;
       clingo_symbol_number(arguments[0], &id_c);
       clingo_symbol_number(arguments[1], &id_a);
       clingo_symbol_create_number(count_zeroes(id_c, id_a), &sym);
       return symbol_callback(&sym, 1, symbol_callback_data);
   }
   clingo_set_error(clingo_error_runtime, "function not found");
   return false;
}
*/
//output: an atom array of a model and its length
bool get_atoms(clingo_model_t const* model, clingo_symbol_t** atoms, size_t* atoms_n) {

    bool ret = true;
    
    
    clingo_symbol_t const* it, * ie;

    // determine the number of (shown) symbols in the model
    if (!clingo_model_symbols_size(model, clingo_show_type_atoms, &(*atoms_n))) { goto error; }

    // allocate required memory to hold all the symbols
    if (!(*atoms = (clingo_symbol_t*)malloc(sizeof(*atoms) * *atoms_n))) {
        clingo_set_error(clingo_error_bad_alloc, "could not allocate memory for atoms");
        goto error;
    }

    // retrieve the symbols in the model
    if (!clingo_model_symbols(model, clingo_show_type_atoms, *atoms, *atoms_n)) { goto error; }

    goto out;

error:
    ret = false;

out:
    //if (atoms) { free(atoms); }

    return ret;

}
//set atoms as facts for another solver/ASP program through its control object
bool set_answerset_atoms_as_facts(clingo_control_t* ctl, clingo_symbol_t* atoms, size_t atoms_n) {
    /*build get atoms*/

    bool ret = true;
    
    
    clingo_symbol_t const* it, * ie;
    clingo_backend_t* backend;

    // get the backend
    if (!clingo_control_backend(ctl, &backend)) { goto error; }

    // prepare the backend for adding rules
    if (!clingo_backend_begin(backend)) { goto error; }


    for (it = atoms, ie = atoms + atoms_n; it != ie; ++it) {
        bool equal;
        clingo_atom_t atom_ptr;

        if (!clingo_backend_add_atom(backend, it, &atom_ptr)) { goto error; }


        if (!clingo_backend_rule(backend, false, &atom_ptr, 1, NULL, 0)) { goto error; }

    }
    // finalize the backend
    if (!clingo_backend_end(backend)) { goto error; }

    goto out;

error:
    ret = false;

out:
    if (atoms) { free(atoms); }

    return ret;
}

//get atoms of a model and set them as facts for another solver/ASP program through its control object
bool set_answerset_model_as_facts(clingo_control_t* ctl, clingo_model_t const* model) {
    /*build get atoms*/

    bool ret = true;
    clingo_symbol_t* atoms;
    size_t atoms_n;
    clingo_symbol_t const* it, * ie;
    clingo_backend_t* backend;

    // get the backend
    if (!clingo_control_backend(ctl, &backend)) { goto error; }

    // prepare the backend for adding rules
    if (!clingo_backend_begin(backend)) { goto error; }


    get_atoms(model, &atoms, &atoms_n);



    for (it = atoms, ie = atoms + atoms_n; it != ie; ++it) {
        bool equal;
        clingo_atom_t atom_ptr;

        if (!clingo_backend_add_atom(backend, it, &atom_ptr)) { goto error; }


        if (!clingo_backend_rule(backend, false, &atom_ptr, 1, NULL, 0)) { goto error; }

    }
    // finalize the backend
    if (!clingo_backend_end(backend)) { goto error; }

    goto out;

error:
    ret = false;

out:
    if (atoms) { free(atoms); }

    return ret;
}
//used to print models for testing
bool print_model(clingo_model_t const* model) {
    bool ret = true;
    clingo_symbol_t* atoms;
    size_t atoms_n;
    clingo_symbol_t const* it, * ie;
    char* str = NULL;
    size_t str_n = 0;



    // determine the number of (shown) symbols in the model
    if (!clingo_model_symbols_size(model, clingo_show_type_shown, &atoms_n)) { goto error; }

    // allocate required memory to hold all the symbols
    if (!(atoms = (clingo_symbol_t*)malloc(sizeof(*atoms) * atoms_n))) {
        clingo_set_error(clingo_error_bad_alloc, "could not allocate memory for atoms");
        goto error;
    }

    // retrieve the symbols in the model
    if (!clingo_model_symbols(model, clingo_show_type_shown, atoms, atoms_n)) { goto error; }

    get_atoms(model, &atoms, &atoms_n);

    for (it = atoms, ie = atoms + atoms_n; it != ie; ++it) {
        size_t n;
        char* str_new;

        // determine size of the string representation of the next symbol in the model
        if (!clingo_symbol_to_string_size(*it, &n)) { goto error; }

        if (str_n < n) {
            // allocate required memory to hold the symbol's string
            if (!(str_new = (char*)realloc(str, sizeof(*str) * n))) {
                clingo_set_error(clingo_error_bad_alloc, "could not allocate memory for symbol's string");
                goto error;
            }

            str = str_new;
            str_n = n;
        }

        // retrieve the symbol's string
        if (!clingo_symbol_to_string(*it, str, n)) { goto error; }

        printf(" %s", str);
    }

    printf("\n");
    goto out;

error:
    ret = false;

out:
    if (atoms) { free(atoms); }
    if (str) { free(str); }

    return ret;
}


//solves on single ASP. Can be used to put method in atoms array as an output
bool singleshot_solve_asp(clingo_control_t* ctl, bool only_first, clingo_solve_result_bitset_t* result, clingo_symbol_t*** atoms_array, size_t** atom_array_size) {
    bool ret = true;
    clingo_solve_handle_t* handle;
    clingo_model_t** help_v;
    size_t index = 0;
    int i = 0;
    clingo_model_t const* model;

    //if only_first is false the ASP is only checked on satisfiability 
    if (!(only_first)) {
        if (!(*atoms_array = malloc(sizeof(*atoms_array)))) {
            clingo_set_error(clingo_error_bad_alloc, "could not allocate memory for atoms");

        }
        if (!(*atom_array_size = malloc(sizeof(*atom_array_size)))) {
            clingo_set_error(clingo_error_bad_alloc, "could not allocate memory for atoms");

        }



        clingo_id_t root_key, sub_key;
        clingo_configuration_t* conf;
        // get the configuration object and its root key
        if (!clingo_control_configuration(ctl, &conf)) { goto error; }
        if (!clingo_configuration_root(conf, &root_key)) { goto error; }

        // configure to enumerate all models
        if (!clingo_configuration_map_at(conf, root_key, "solve.models", &sub_key)) { goto error; }
        if (!clingo_configuration_value_set(conf, sub_key, "0")) { goto error; }


        // get a solve handle
        if (!clingo_control_solve(ctl, clingo_solve_mode_yield, NULL, 0, NULL, NULL, &handle)) { goto error; }

        // loop over all models
        while (true) {





            if (!clingo_solve_handle_resume(handle)) { goto error; }
            if (!clingo_solve_handle_model(handle, &model)) { goto error; }
            // print the model
            if (model) {
                i++;

                if (!(*atoms_array = realloc(*atoms_array, sizeof(*atoms_array) * (i + 1)))) {
                    clingo_set_error(clingo_error_bad_alloc, "could not allocate memory");
                    goto error;
                }
                if (!(*atom_array_size = realloc(*atom_array_size, sizeof(*atom_array_size) * (i + 1)))) {
                    clingo_set_error(clingo_error_bad_alloc, "could not allocate memory");
                    goto error;
                }


                get_atoms(model, *atoms_array + i, *atom_array_size + i);


            }
            else { break; }

            **atom_array_size = i;
        }


        
    }
    else
    {
        //checks only satisfiability of ASP program
        if (!clingo_control_solve(ctl, clingo_solve_mode_yield, NULL, 0, NULL, NULL, &handle)) { goto error; }

        

    }



    if (!clingo_solve_handle_get(handle, result)) { goto error; }

    if (*result == 2 || *result == 6) {
        *result = 2;
    }
    if (*result == 1 || *result == 5) {
        *result = 1;
    }

    goto out;

error:
    ret = false;

out:
    
    //if (str) { free(str); }
    // free the solve handle
    return clingo_solve_handle_close(handle) && ret;
}

//used to create control object for the solver
bool create_control(clingo_control_t** ctl, bool single_model, const char* load_file) {
    bool ret = true;
    
    clingo_configuration_t* conf;
    clingo_id_t root_key, sub_key;

    if (!clingo_control_new(NULL, 0, NULL, NULL, 0, ctl) != 0) { goto error; }

    // get the configuration object and its root key
    if (!clingo_control_configuration(*ctl, &conf)) { goto error; }
    if (!clingo_configuration_root(conf, &root_key)) { goto error; }

    if (!single_model)
    {
        // configure to enumerate all models
        if (!clingo_configuration_map_at(conf, root_key, "solve.models", &sub_key)) { goto error; }
        if (!clingo_configuration_value_set(conf, sub_key, "0")) { goto error; }
    }
 

    //if (!clingo_configuration_map_at(conf, root_key, "solve.parallel_mode", &sub_key)) { goto error; }
    //if (!clingo_configuration_value_set(conf, sub_key, "8,compete")) { goto error; }

    if (load_file != NULL)
    {
        if (!clingo_control_load(*ctl, load_file)) { goto error; }
    }

    goto out;

error:
    ret = false;

out:

    return ret;
}



//used for skeptical controllability checking and completion checking for credulous controlllability
bool multishot_solve_result(clingo_control_t* ctl, clingo_solve_result_bitset_t* result, const char* file, const char* filter, int mode) {

    bool ret = true;
    clingo_solve_handle_t* handle;
    clingo_model_t const* model;
    
    clingo_ground_callback_t callback_f = NULL;
    clingo_part_t parts_cred[] = { { "extension", NULL, 0 }, { "credulous", NULL, 0 }, { filter, NULL, 0 } };
    clingo_part_t parts_skept[] = { { "completion", NULL, 0 }, { "extension", NULL, 0 }, { "skeptical", NULL, 0 }, { filter, NULL, 0 } };
    clingo_part_t* parts = NULL;
    int parts_size = 0;
    

    *result = 0;
    if (mode == 1) {
        parts = parts_cred;
        parts_size = 3;

    }
    else {
        parts = parts_skept;
        parts_size = 4;

    }


    // get a solve handle
    if (!clingo_control_solve(ctl, clingo_solve_mode_yield, NULL, 0, NULL, NULL, &handle)) { goto error; }


    
    //models get checked in a loop. this could be packed in a method and run parallel
    while (true) {

        

        if (!clingo_solve_handle_resume(handle)) { goto error; }
        if (!clingo_solve_handle_model(handle, &model)) { goto error; }

        
        
        // print the model
        if (model && (*result != 2)) {
            clingo_control_t* ctl_second_lvl = NULL;
            clingo_symbol_t** atoms_array_second_lvl;
            size_t* atom_array_size_second_lvl;
            clingo_solve_result_bitset_t result_second_lvl;
          
            if (!create_control(&ctl_second_lvl, true, file)) { goto error; }



            if (!set_answerset_model_as_facts(ctl_second_lvl, model)) { goto error; };

            


            
            //grounding of ASP programms and models of previous ASP
            if (!clingo_control_ground(ctl_second_lvl, parts, parts_size, callback_f, NULL)) { goto error; }


            
            //solves ASP and gives result to satisfiability of second lvl ASPs
            if (!singleshot_solve_asp(ctl_second_lvl, true, &result_second_lvl, NULL, NULL)) { goto error; }

            if (ctl_second_lvl) { clingo_control_free(ctl_second_lvl); }
            
            
           
            //the solver adds 4 to the result bits if all the models were checked
            if (result_second_lvl == 1 || result_second_lvl == 5) {
                *result = 1;
            }
            if (result_second_lvl == 2 || result_second_lvl == 6) {
                *result = 2;
            }
        }
        else {
            break;
        }

        
        
    }

    

    if (*result == 2 || *result == 6) {
        *result = 2;
    }
    if (*result == 1 || *result == 5) {
        *result = 1;
    }

    goto out;

error:
    ret = false;

out:
    // free the solve handle
    if (handle) { clingo_solve_handle_close(handle); }
    if (ctl) { clingo_control_free(ctl); }
    return ret;
}


//used for credulous controllability solving. uses multishot_solve_result method for second and third lvl ASP solving (for checking of completions and its extensions)
bool multishot_solve_cred(clingo_control_t* ctl, clingo_solve_result_bitset_t* result, const char* file, const char* filter) {
    bool ret = true;
    clingo_solve_handle_t* handle;
    clingo_model_t const* model;
    size_t model_symbols_size;
    clingo_symbol_t*** atoms_array_pointer;
    size_t** atom_array_size_pointer;
    clingo_solve_result_bitset_t result_second_lvl = 2;
    clingo_part_t parts[] = { { "completion", NULL, 0 } };
    clingo_part_t second_lvl_parts[] = { { "extension", NULL, 0 }, { "credulous", NULL, 0 }, { filter, NULL, 0 } };


    // get a solve handle
    if (!clingo_control_solve(ctl, clingo_solve_mode_yield, NULL, 0, NULL, NULL, &handle)) { goto error; }

 

    


    while (true) {
        if (!clingo_solve_handle_resume(handle)) { goto error; }
        if (!clingo_solve_handle_model(handle, &model)) { goto error; }



        // run through models. can be packed together in a method for parallel run
        if (model) {


            clingo_control_t* ctl_second_lvl = NULL;
            result_second_lvl = 0;
            clingo_symbol_t** atoms_array_second_lvl;
            size_t* atom_array_size_second_lvl;

            if (!create_control(&ctl_second_lvl, false, file)) { goto error; }

            

            if (!set_answerset_model_as_facts(ctl_second_lvl, model)) { goto error; };


            


            if (!clingo_control_ground(ctl_second_lvl, parts, 1, NULL, NULL)) { goto error; };


            


            if (!multishot_solve_result(ctl_second_lvl, &result_second_lvl, file, filter,1)) { goto error; }


            

           
            if (result_second_lvl == 1 || result_second_lvl == 5) {
                *result = result_second_lvl;
                break;
            }



        }
        // stop if there are no more models
        else {
            break;
        }


    }

    

    // close the solve handle
    if (!clingo_solve_handle_get(handle, result)) { goto error; }
    // 4 gets added to the result bit if all models got checked. 1 = satisfiable 2 = unsatisfiable
    if (result_second_lvl == 2 || result_second_lvl == 6) {
        *result = 2;
    }
    if (result_second_lvl == 1 || result_second_lvl == 5) {
        *result = 1;
    }

    goto out;

error:
    ret = false;

out:
    
    // free
    if (handle) { clingo_solve_handle_close(handle); }
    if (ctl) { clingo_control_free(ctl); }
    return ret;
}









//used to solve the skeptican controllability problem for stable semantics. 
bool multishot_solve_skept_st(clingo_control_t* ctl, clingo_solve_result_bitset_t* result, const char* file, const char* filter) {
    bool ret = true;
    clingo_solve_handle_t* handle;
    clingo_model_t const* model;
    size_t model_symbols_size;
    clingo_symbol_t*** atoms_array_pointer;
    size_t** atom_array_size_pointer;
    clingo_solve_result_bitset_t result_second_lvl = 2;
    clingo_ground_callback_t callback_f = NULL;
    clingo_part_t parts[] = { { "completion", NULL, 0 }, { "extension", NULL, 0 },  { filter, NULL, 0 } };
    clingo_part_t part_skeptical[] = { { "skeptical", NULL, 0 }};
    bool min_on_ext_st = false;

    // get a solve handle
    if (!clingo_control_solve(ctl, clingo_solve_mode_yield, NULL, 0, NULL, NULL, &handle)) { goto error; }

    int i = 0;



    while (true) {
        if (!clingo_solve_handle_resume(handle)) { goto error; }
        if (!clingo_solve_handle_model(handle, &model)) { goto error; }



        // print the model
        if (model && (result_second_lvl != 1)) {
            clingo_control_t* ctl_second_lvl = NULL;
            clingo_control_t* ctl_second_lvl_skept = NULL;
            clingo_symbol_t** atoms_array_second_lvl;
            size_t* atom_array_size_second_lvl;
            result_second_lvl = 0;

            if (!create_control(&ctl_second_lvl, true, file)) { goto error; }



            if (!set_answerset_model_as_facts(ctl_second_lvl, model)) { goto error; };

            //satisfiability for completions get checked first. than skeptical controllability get checked on the extensions. the models of the checking get passed to the last solver if it is satisfiable

            if (!clingo_control_ground(ctl_second_lvl, parts, 3, callback_f, NULL)) { goto error; }

            if (!singleshot_solve_asp(ctl_second_lvl, true, &result_second_lvl, &atoms_array_second_lvl, &atom_array_size_second_lvl)) { goto error; }

            if (result_second_lvl == 1 || result_second_lvl == 5) {
                min_on_ext_st = true;
            }

            if (!create_control(&ctl_second_lvl_skept, true, file)) { goto error; }

            if (!set_answerset_atoms_as_facts(ctl_second_lvl_skept, *(atoms_array_second_lvl + (*atom_array_size_second_lvl)), (*atom_array_size_second_lvl) + atom_array_size_second_lvl)) { goto error; }

            if (!clingo_control_ground(ctl_second_lvl_skept, part_skeptical, 1, callback_f, NULL)) { goto error; }

            if (!singleshot_solve_asp(ctl_second_lvl_skept, true, &result_second_lvl, &atoms_array_second_lvl, &atom_array_size_second_lvl)) { goto error; }
            

            if (result_second_lvl == 1 || result_second_lvl == 5) {
                *result = result_second_lvl;
            }
        }
        else {
            break;
        }
    }



    // close the solve handle
    if (!clingo_solve_handle_get(handle, result)) { goto error; }

    if (result_second_lvl == 2 || result_second_lvl == 6) {
        *result = 2;
    }
    if (result_second_lvl == 1 || result_second_lvl == 5) {
        *result = 1;
    }
    if (min_on_ext_st) {
        *result = 2;
    }
    goto out;

error:
    ret = false;

out:
    // free the solve handle
    return clingo_solve_handle_close(handle) && ret;
}





//user INPUT for argv: (1) Path of ASP programs, that implement problem solving;(2) Path of files of facts for the problem; OUTPUT: (1) Time for solving
double main(int argc, char const** argv) {
    
    char const* error_message;
    double elapsed = 0;
    clingo_solve_result_bitset_t solve_ret;
    clingo_control_t* ctl = NULL;

    //ASP Programs as first input of programm
    const char* asp_file = *(argv + 1);

    //Input for the ASP programs as a set of facts
    const char* asp_file_input_CAF = *(argv + 2);

     

    double start = clock();
    
 
   //solver control object gets created. if intern parallel running of clingo is desired check the implementation of method
    if (!create_control(&ctl, false, asp_file)) { goto error; }


    //loads facts for solver
    if (!clingo_control_load(ctl, asp_file_input_CAF)) { goto error; }
    
    //grounds set of facts for the solver. preparation to call base programm of inputs
    clingo_part_t configs[] = { { "base", NULL, 0 } };
    //grounds set of facts for the solver
    if (!clingo_control_ground(ctl, configs, 1, NULL, NULL)) { goto error; }


    

    //the first method here is used to solve credulous controllability. if skeptical controllability is desired than this should be commented out before compiling and the next line should be uncommented instead
    //to change semantics the name of the semantic should be changed after filter_
    if (!multishot_solve_cred(ctl, &solve_ret, asp_file, "filter_complete")) { goto error; };

    //checks skeptical controllability except stable. for stable semantic checking the method multishot_solve_skept_st should be used, because of empty set definition of stable semantics
    //if (!multishot_solve_result(ctl, &solve_ret, asp_file, "filter_complete",2)) { goto error; };;

    double end = clock();
    elapsed = (end - start) / CLOCKS_PER_SEC;
    printf("%f", elapsed);


    //can be used to check results through printf
    if (solve_ret == 1) {
        //printf("skept:NOT CONTROLLABLE cred:CONTROLLABLE");
    }
    else {
        //printf("skept:CONTROLLABLE cred:NOT CONTROLLABLE");
    }

    
    

    
    
    goto out;

error:
    if (!(error_message = clingo_error_message())) { error_message = "error"; }

    printf("%s\n", error_message);
    //ret = clingo_error_code();

out:
    //if (ctl) { clingo_control_free(ctl); }

    return elapsed;
}




