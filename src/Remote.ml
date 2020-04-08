let perform_rpc_action ~address ~port ~json =
    let handle = Curl.init ()
    in
        let response = ref ""
        and response_assignment_fun = (fun bf str -> bf:=str; String.length str)
        in
            Curl.setopt handle (Curl.CURLOPT_URL (address^":"^port) );
            Curl.setopt handle (Curl.CURLOPT_POSTFIELDS json);
            Curl.setopt handle (Curl.CURLOPT_HTTPHEADER ["Content-Type: application/json"]);
            Curl.setopt handle (Curl.CURLOPT_WRITEFUNCTION (response_assignment_fun response ) ) ;
            Curl.perform handle ;
            Curl.cleanup handle;
            !response
type rpc_resp = {msg:bool ; id:int}        

let parse_rpc_response str_resp = 
    let jsn_resp = Yojson.Basic.from_string str_resp
    in
        { 
            msg = jsn_resp |> Yojson.Basic.Util.member "result" |> Yojson.Basic.Util.to_bool;
            id = jsn_resp |> Yojson.Basic.Util.member "id" |> Yojson.Basic.Util.to_int
        }
let remote_equal ~address ~port b1 b2 =
    let b1_json = Digraph.big_2_dig b1 |> Dig2Json.dig_to_json
    and b2_json = Digraph.big_2_dig b2 |> Dig2Json.dig_to_json
    in
        let payload = `Assoc 
        [
            ("method", `String "iso");
            ("params", `Assoc 
                [
                    ("graph1", `String (b1_json |> Yojson.Basic.to_string)  );
                    ("graph2", `String (b2_json |> Yojson.Basic.to_string) );
                ]
            );
            ("jsonrpc", `String "2.0");
            ("id", `Int 0);
        ] |> Yojson.Basic.to_string
        in
            let result = perform_rpc_action ~address ~port ~json:payload  |> parse_rpc_response
            in
                result.msg