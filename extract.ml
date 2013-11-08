(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

module UF = struct
  type t = int array
  let create n = Array.init n (fun i -> i) 
  let repr t i =
    let rec aux k l =
      if t.(k) = k 
      then (List.iter (fun i -> t.(i) <- k) l; k)
      else aux (t.(k)) (k::l)
    in
    aux i []
  let union t i j =
    let e = repr t i in 
    let f = repr t j in 
    t.(e) <- f
  let canonize t =
    let u = Array.create (Array.length t) (None) in 
    let _ = 
      let n = ref 0 in 
      for i = 0 to Array.length t - 1 do
	t.(i) <- repr t i;
	if t.(i) = i then 
	  begin 
	    incr n;
	    u.(i) <- Some !n
	  end
      done;
    in
    let rec unopt i x = match x with | Some a -> a | None -> unopt (repr t i) (u.(repr t i)) in
    Array.mapi unopt u
end
    
type instance =
    {
      uid : int;
      door : string;
      wire_in : int list;
      wire_out : int list;
    }

let beautify_dump (instances,wires,n,inputs, outputs) =
  let uf = UF.create n in 
  let _ = List.iter (fun (a,b) -> UF.union uf a b) wires in 
  let uf = UF.canonize uf in 
  let f x = uf.(x) in
  let instances = 
    List.map (fun a -> {a with wire_in = List.map f a.wire_in; wire_out = List.map f a.wire_out}) instances in 
  let inputs = List.map f inputs in 
  let outputs = List.map f outputs in 
  instances, inputs, outputs
;;

let dump_xor =
  let _,instances =
    List.fold_left (fun (fresh,acc)(i,o) -> 
      fresh + 1, 
      {
	uid = fresh;
	door = "nor"; 
	wire_in = i;
	wire_out = o
      } :: acc)
      (0,[])
      [[19;20],  [21];
       [24;25],  [26];
       [35;36],  [37];
       [38;39],  [40];
       [41;42],  [43]
      ]
  in
  let wires =
    [(0, 9);(0, 10);(1, 11);(1, 12);(9, 13);(10, 14);
          (11, 15);(12, 16);(13, 17);(13, 18);(17, 19);
          (18, 20);(21, 5);(14, 6);(15, 22);(15, 23);
          (22, 24);(23, 25);(26, 7);(16, 8);(5, 27);
          (7, 28);(6, 29);(8, 30);(27, 31);(28, 32);
          (29, 33);(30, 34);(31, 35);(32, 36);(37, 3);
          (33, 38);(34, 39);(40, 4);(3, 41);(4, 42);
          (43, 2)]
  in 
  instances, wires, 44, [0;1], [2]
;;

let _ = beautify_dump dump_xor ;;
let _ = ()

module VHDL = struct
  let comment fmt s = Format.fprintf fmt "-- %s@\n" s 
  let port_out fmt o = 
    Format.fprintf fmt "x%i\t:\tout bit" o
  let port_in fmt i = 
    Format.fprintf fmt "x%i\t:\tin bit" i
  let port fmt i =
    Format.fprintf fmt "%s" i

  let print_list f fmt l =
    List.iter (Format.fprintf fmt "%a@\n" f) l
  let print_list_sep sep f fmt l =
    let rec aux fmt = function
      | [] -> ()
      | [t] -> Format.fprintf fmt "%a" f t
      | t::q -> Format.fprintf fmt "%a%s%a" f t sep aux q
    in 
    aux fmt l

  let ports fmt (inputs,outputs) = 
    comment fmt "clock";
    Format.fprintf fmt "clk\t:\tin bit@\n";
    comment fmt "inputs";
    Format.fprintf fmt "%a" (print_list port_in) inputs ;
    comment fmt "outputs";
    Format.fprintf fmt "%a" (print_list port_out) outputs;
    ()

  let entity fmt name inputs outputs =
    Format.fprintf fmt "entity\n\t%s\nis\n" name;
    Format.fprintf fmt "port\n(\n@[<v>@\n%a@]\n)\n" ports (inputs,outputs);
    Format.fprintf fmt "end entity %s;\n" name
      
  let signal fmt signal = 
    Format.fprintf fmt "signal x%i : bit;" signal
    
  let instance fmt i = 
    let wires = i.wire_in @ i.wire_out in 
    let wires = List.map (fun x -> Format.sprintf "x%i" x) wires in 
    let wires = "clk" :: wires in 
    Format.fprintf fmt "door_%i : entity %s port map (%a)" i.uid i.door 
      (print_list_sep "," port) wires
      
  let architecture fmt name signals instances =
    Format.fprintf fmt "architecture structural of %s\n" name;
    Format.fprintf fmt "is\n@[<v>@\n%a@]\n" (print_list signal) signals;
    Format.fprintf fmt "begin\n@[<v>@\n%a@]\nend structural\n" (print_list instance) instances;
    ()

  let dump fmt name signals instances inputs outputs =
    comment fmt "Generated from Coq";
    entity fmt name inputs outputs;
    Format.fprintf fmt "\n";
    comment fmt "Architecture";
    architecture fmt name signals instances

end

module Int = struct 
  type t = int 
  let equal = (=) 
  let compare = Pervasives.compare 
end

module IntSet = Set.Make(Int);;

let add s l = List.fold_right IntSet.add l s

  
let dump fmt (instances,inputs,outputs) = 
  let signals = List.fold_left 
    (fun acc i -> 
      add acc (i.wire_in @ i.wire_out)
    ) IntSet.empty instances 
  in
  let signals = IntSet.elements signals in 
  VHDL.dump fmt "xor" signals instances inputs outputs
;;
let _ = Format.printf "%a" dump (beautify_dump dump_xor)
let _ = 
  let o = open_out "test.vhd" in 
  let fmt = Format.formatter_of_out_channel o in 
  Format.fprintf fmt "%a" dump (beautify_dump dump_xor);
  close_out o

let _ = ()
(* writeDefinitions :: (Generic a, Generic b)
                 => FilePath -> String -> a -> b -> b -> IO ()
writeDefinitions file name inp out out' =
  do firstHandle  <- openFile firstFile WriteMode
     secondHandle <- openFile secondFile WriteMode
     var <- newIORef 0

     hPutStr secondHandle $ unlines $
       [ "begin"
       ]

     let new =
           do n <- readIORef var
              let n' = n+1; v = "w" ++ show n'
              writeIORef var n'
              hPutStr firstHandle ("  signal " ++ v ++ " : bit;\n")
              return v

         define v s =
           case s of
             Bool True     -> port "vdd"  []
             Bool False    -> port "gnd"  []
             Inv x         -> port "inv"  [x]

             And []        -> define v (Bool True)
             And [x]       -> port "id"   [x]
             And [x,y]     -> port "and2" [x,y]
             And (x:xs)    -> define (w 0) (And xs)
                           >> define v (And [x,w 0])

             Or  []        -> define v (Bool False)
             Or  [x]       -> port "id"   [x]
             Or  [x,y]     -> port "or2"  [x,y]
             Or  (x:xs)    -> define (w 0) (Or xs)
                           >> define v (Or [x,w 0])

             Xor  []       -> define v (Bool False)
             Xor  [x]      -> port "id"   [x]
             Xor  [x,y]    -> port "xor2" [x,y]
             Xor  (x:xs)   -> define (w 0) (Or xs)
                           >> define (w 1) (Inv (w 0))
                           >> define (w 2) (And [x, w 1])

                           >> define (w 3) (Inv x)
                           >> define (w 4) (Xor xs)
                           >> define (w 5) (And [w 3, w 4])
                           >> define v     (Or [w 2, w 5])

             VarBool s     -> port "id" [s]
             DelayBool x y -> port "delay" [x, y]

             _             -> wrong Lava.Error.NoArithmetic
           where
            w i = v ++ "_" ++ show i

            port name args =
              do hPutStr secondHandle $
                      "  "
                   ++ make 9 ("c_" ++ v)
                   ++ " : entity "
                   ++ make 5 name
                   ++ " port map ("
                   ++ concat (intersperse ", " ("clk" : args ++ [v]))
                   ++ ");\n"

     outvs <- netlistIO new define (struct out)
     hPutStr secondHandle $ unlines $
       [ ""
       , "  -- naming outputs"
       ]

     sequence
       [ define v' (VarBool v)
       | (v,v') <- flatten outvs `zip` [ v' | VarBool v' <- outs' ]
       ]

     hPutStr secondHandle $ unlines $
       [ "end structural;"
       ]

     hClose firstHandle
     hClose secondHandle

     system ("cat " ++ firstFile ++ " " ++ secondFile ++ " > " ++ file)
     system ("rm " ++ firstFile ++ " " ++ secondFile)
     return ()
 where
  sigs x = map unsymbol . flatten . struct $ x

  inps  = sigs inp
  outs' = sigs out'

  firstFile  = file ++ "-1"
  secondFile = file ++ "-2"

  make n s = take (n `max` length s) (s ++ repeat ' ')


*)
