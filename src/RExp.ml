
let _default_file_name () = 
    ( ( string_of_float (Unix.time ()) )^".csv")
let export_ss_csv ?(trans_file_name= "trans_"^_default_file_name () ) ?(states_file_name = "states_"^_default_file_name () ) its ius =
    let trans_header = TBrs.trans_header  
    and states_header = TBrs.states_header in
    let transitions = trans_header :: TBrs.transistions_to_losl its
    and states = states_header :: TBrs.states_to_losl ius
    in
        Csv.save trans_file_name transitions;
        Csv.save states_file_name states
