open List
open Float
open Format

open Interp
open Printing
open Tree
open Stepfunction
open Segment
open Interval
open Util
open Parse
open Memory

(* Testing functions *)
(* ---------------------- *)
let test (b : bool) (m : string) = if not b then failwith m ;;

let test_eq (a1 : 'a) (a2 : 'a) (m : string) = test (a1 = a2) m ;;

let test_in vals lst =
    (fold_left (fun acc i -> acc && exists (fun x -> i = x) lst)
                      true vals) ;;
                      
let test_tuple input output tst m = 
    let (in1, in2) = input in
    let (out1, out2) = output in
    tst in1 out1 (m ^ " on first operand") ;
    tst in2 out2 (m ^ " on second operand") ;;

let test_bool input output m = test_tuple input output test_eq m ;;

let equal_lsts lst vals = (test_in vals lst && test_in lst vals) ;;
let test_lst lst vals m = test (equal_lsts lst vals) m ;;
let test_tup_lst ins outs = test_tuple ins outs test_lst ;;
let test_sfs sf1 sf2 m = test_lst (get_segs sf1) (get_segs sf2) m ;;
let test_sfs_b input output m = test_tuple input output test_sfs m ;;

(* Util Testing *)
(* ---------------------- *)

let xs = [ 1 ; 1 ; 2 ; ] ;;
let ys = [ 2 ; 4 ; 8 ; ] ;;
let out = [ 3 ; 5 ; 9 ; 3 ; 5; 9 ; 4 ; 6 ; 10 ];;

let product_map_test () =
    test_lst out (product_map (+) xs ys) "product_map failed test" ;;


let extremes_test () = 
    let lst = [ 5. ; 6. ; 1.4; 2.2 ] in
    test_eq 1.4 (min_flt lst) "min_flt failed test" ;
    test_eq 6. (max_flt lst) "max_flt failed test" ;;


let last_test () =
    test_eq 1 (last [2 ; 1]) "last failed test" ;;


let remove_last_test () =
    test_eq [1 ; 2 ; 3 ; 4] 
            (remove_last [1; 2; 3; 4; 5]) 
            "remove_last failed test" ;;

let util_testing () = 
    product_map_test () ;
    extremes_test () ;
    last_test () ;
    remove_last_test () ;;

(* Interval Testing *)
(* ---------------------- *)
let i1 = intr_of 2. 4. ;;
let i2 = intr_of 4. 8. ;;
let i3 = intr_of 1. 3. ;;
let i4 = intr_of (-5.) 3. ;;
let i5 = intr_of 1. 5. ;;
let i6 = intr_of 3. 4. ;;

let intr_of_test () =
    test_eq i1 (Intr { l = 2. ; u = 4. })
         "intr_of doesn't construct correct interval" ;
    test_eq (intr_of 2. 1.) IntrBot
         "intr_of doesn't default to bottom" ;;


let intr_contains_test () =
    test (contains i1 2.) "contains doesn't capture lower bound" ;
    test (contains i1 3.) "contains doesn't capture inner value" ;
    test (contains i1 4.) "contains doesn't capture upper bound" ;
    test (not (contains i1 5.)) "contains returns true for uncontained value" ;;


let intr_adjacent_test () =
    test (not (intr_adjacent i1 i1)) "intr_adjacent includes same interval" ;
    test (not (intr_adjacent i1 i2)) "intr_adjacent includes overlapping upper bound" ;
    test (not (intr_adjacent i2 i1)) "intr_adjacent includes overlapping lower bound" ;
    test (intr_adjacent i1 (intr_of 1. (Float.pred (lower i1)))) "intr_adjacent misses lower bound" ;
    test (intr_adjacent i1 (intr_of (Float.succ (upper i1)) 5.)) "intr_adjacent misses upper bound" ;
;;


let intr_overlap_test () =
    test (intr_overlap i1 i3) 
         "intr_overlap doesn't identify overlapping intervals" ;
    test (intr_overlap i1 i2)
         "intr_overlap doesn't identify intervals it same boundary" ;
    test (not (intr_overlap i2 i3))
         "intr_overlap identifies non-overlapping intervals" ; 
    test (intr_overlap i1 i5) 
        "intr_overlap doesn't identify containing overlap" ;;


let intr_ops_test () =
    test_eq (intr_add i1 i2) (intr_of 6. 12.) "intr_add failed" ;
    test_eq (intr_sub i1 i2) (intr_of (-6.) 0.) "intr_sub failed" ;
    test_eq (intr_mul i1 i2) (intr_of 8. 32.) "intr_mul failed" ;
    test_eq (intr_div i2 i1) (intr_of 1. 4.) "intr_div failed" ;;


let intr_mags_test () =
    test_eq (mag_lg_intr i1) 4. "mag_lg_intr failed" ;
    test_eq (mag_lg_intr i4) 5. "mag_lg_intr failed with negative numbers" ;
    test_eq (mag_sm_intr i1) 2. "mag_sm_intr failed" ;
    test_eq (mag_sm_intr (intr_of (-5.) (-2.))) 2. "mag_sm_intr failed cross 0 test" ;
    test_eq (mag_sm_intr i4) 0. "mag_sm_intr failed cross 0 test" ;;


let intr_split_binade_test () =
    test_lst (split_binade (intr_of 0.4 9.)) 
             [intr_of 0.4 (pred 0.5); intr_of 0.5 (pred 1.) ;
              intr_of 1. (pred 2.) ; intr_of 2. (pred 4.) ;
              intr_of 4. (pred 8.) ; intr_of 8. 9. ]
             "split_binade failed happy path test" ;
    test_lst (split_binade (intr_of 0.4 8.)) 
             [intr_of 0.4 (pred 0.5); intr_of 0.5 (pred 1.) ;
              intr_of 1. (pred 2.) ; intr_of 2. (pred 4.) ;
              intr_of 4. (pred 8.) ; intr_of 8. 8. ]
             "split_binade failed edge test" ;
    test_lst (split_binade (intr_of 0.124 2.)) 
             [intr_of 0.124 (pred 0.125); intr_of 0.125 (pred 0.25) ;
              intr_of 0.25 (pred 0.5) ; intr_of 0.5 (pred 1.0) ;
              intr_of 1.0 (pred 2.) ; intr_of 2. 2. ]
             "split_binade failed negative exponents test" ;
    test_lst (split_binade (intr_of (-4.) (-0.4)))
             [intr_of (-4.) (-4.) ; intr_of (succ (-4.)) (-2.) ; 
              intr_of (succ (-2.)) (-1.) ; intr_of (succ (-1.)) (-0.5) ;
              intr_of (succ (-0.5)) (-0.4) ]
             "split_binade failed negative values test" ;
    test_lst (split_binade (intr_of (-2.1) (1.9))) 
             ((split_binade (intr_of (-2.1) (pred 0.))) @ 
              [intr_of (-0.) 0.] @
              (split_binade (intr_of (succ 0.) 1.9)))
             "split_binade failed crossing 0 test" ;
    test_eq (length (split_binade (intr_of 0. 1.)))
             (1024)
             "split_binade failed positive 0 boundary test" ;
    test_eq (length (split_binade (intr_of (-1.) 0.)))
             (1024)
             "split_binade failed negative 0 boundary test" ;
    test_lst (split_binade (intr_of 3. 3.5)) 
             [intr_of 3. 3.5]
             "split_binade failed one-binade test" ;;

let intr_lt_test () =
    test_bool (intr_lt i3 i1) (i3, i1) "intr_lt failed no-change test" ;
    test_bool (intr_lt i1 i4) (intr_of (lower i1) (upper i4 -. ulp (upper i4)), 
                               intr_of (lower i1 +. ulp (lower i1)) (upper i4))
              "intr_lt failed boundary test" ;
    test_bool (intr_lt i5 i1) (intr_of (lower i5) ((upper i1) -. ulp (upper i1)), i1) 
              "intr_lt failed overlap test" ;; 


let intr_le_test () =
    test_bool (intr_le i3 i1) (i3, i1) "intr_le failed no-change test" ;
    test_bool (intr_le i1 i4) (intr_of (lower i1) (upper i4), 
                               intr_of (lower i1) (upper i4))
              "intr_le failed boundary test" ;
    test_bool (intr_le i5 i1) (intr_of (lower i5) (upper i1), i1) 
              "intr_le failed overlap test" ;; 


let intr_gt_test () =
    test_bool (intr_gt i3 i1) (intr_of ((lower i1) +. ulp (lower i1)) (upper i3),
                               intr_of (lower i1) ((upper i3) -. ulp (upper i3)))
              "intr_gt failed overlap test" ;
    test_bool (intr_gt i2 i1) (i2, i1) "intr_gt failed no-change test" ;;
    test_bool (intr_gt i5 i1) (intr_of ((lower i1) +. ulp (lower i1)) (upper i5), i1) 
              "intr_gt failed overlap test" ;;


let intr_ge_test () =
    test_bool (intr_ge i3 i1) (intr_of (lower i1) (upper i3), 
                               intr_of (lower i1) (upper i3))
              "intr_ge failed overlap test" ;
    test_bool (intr_ge i2 i1) (i2, i1) "intr_ge failed no-change test" ;;
    test_bool (intr_ge i5 i1) (intr_of (lower i1) (upper i5), i1) 
              "intr_ge failed overlap test" ;;


let intr_eq_test () = 
    let out = intr_of (lower i1) (upper i3) in
    test_bool (intr_eq i1 i3) (out, out) "intr_eq test failed" ;;


let intr_neq_test () = 
    test_bool (intr_neq i1 i2) (i1, i2) "intr_neq test failed" ;;


let intr_union_test () = 
    test_eq (intr_union i1 i2) (intr_of (lower i1) (upper i2)) "intr_union test failed" ;
    test_eq (intr_union i5 i1) i5 "intr_union overlap test failed" ;;


let intr_partition_test () = 
    test_eq (intr_partition i3 i2) ([i3], IntrBot) 
            "intr_partition failed no-change test" ;
    test_eq (intr_partition i5 i1) 
            ([intr_of 1. (pred 2.) ; intr_of (succ 4.) 5.], i1)
            "intr_partition failed containing test" ;
    test_eq (intr_partition i3 i1) 
            ([intr_of 1. (pred 2.)], intr_of 2. 3.) 
            "intr_partition failed overlap test" ;
    test_eq (intr_partition i1 i5) ([], i1)
            "intr_partition failed enveloped test" ;
    test_eq (intr_partition i6 i1) ([], i6)
            "intr_partition failed boundary test" ;;


let intr_with_test () =
    test_eq (intr_with i1 i2) IntrBot "intr_with failed test" ;;

let intr_without_test () =
    test_eq (intr_without i3 i2) [i3] "intr_without failed no-change test" ;
    test_eq (intr_without i5 i1) [intr_of 1. (pred 2.) ; intr_of (succ 4.) 5.] 
        "intr_without failed containing test" ;
    test_eq (intr_without i3 i1) [intr_of 1. (pred 2.)] 
        "intr_without failed overlap test" ;
    test_eq (intr_without i1 i5) [] 
        "intr_without failed enveloped test" ;
    test_eq (intr_without i6 i1) [] 
        "intr_without failed boundary test" ;;

let intr_testing () =
    intr_of_test() ;
    intr_contains_test () ;
    intr_adjacent_test () ;
    intr_overlap_test () ;
    intr_ops_test () ;
    intr_mags_test () ;
    intr_split_binade_test () ;
    intr_lt_test () ;
    intr_le_test () ;
    intr_gt_test () ;
    intr_ge_test () ;
    intr_eq_test () ;
    intr_neq_test () ;
    intr_union_test () ;
    intr_partition_test () ;
    intr_with_test () ;
    intr_without_test () ;;
    

(* Segment Testing *)
(* ---------------------- *)
let s1 = seg_of 2. 4. 0.03;;
let s2 = seg_of 4. 8. 0.101;;
let s3 = seg_of 1. 3. 0.004;;
let s4 = seg_of (-5.) 3. 0.0002 ;;
let s5 = seg_of 1. 5. 0.00202;;

let seg_of_test () = 
    test_eq s1 { int = Intr { l = 2. ; u = 4. }; err = 0.03 } 
        "seg_of failed test" ;
    test_eq (seg_of 3. 2. 0.0001) seg_bot 
        "seg_of did not produce bottom from negative interval" ;
    test_eq (seg_of 1. 2. (-1.)) seg_bot 
        "seg_of did not produce bottom from negative error" ;;


let seg_overlap_test () = 
    test (seg_overlap s1 s3)
        "seg_overlap did not identifiy overlapping segments" ;
    test (not (seg_overlap s2 s4))
        "seg_overlap misidentified unoverlapping segments" ;
    test (seg_overlap s2 (seg_of 3. 12. 0.012)) 
        "seg_overlap misidentified containing overlap" ;;
 

let seg_with_test () =
    test_eq (seg_with s1 s2) seg_bot "seg_with failed test" ;;
    

let seg_partition_test () =
    let (non_overlap, overlap) = seg_partition s2 s1 in
    test_lst non_overlap [seg_of (succ 4.) 8. 0.101] "seg_partition failed overlap test" ;
    test_eq overlap seg_bot "seg_partition failed non-overlap test" ;;


let seg_get_sterbenz_test () =
    test_eq (get_sterbenz_seg s1) (seg_of 2. 4. 0.03) "get_sterbenz_seg failed test" ;;


(*
let seg_op_tests () =
    let t1 = seg_add s1 s2 in
    let t2 = seg_sub s1 s2 in
    let t3 = seg_mul s1 s2 in
    let t4 = seg_div s2 s1 in
    test_lst t1 [seg_of 6. (pred 8.) (err_add s1 s2 (intr_of 6. (pred 8.))) ;
                 seg_of 8. 12. (err_add s1 s2 (intr_of 8. 12.))]
        "seg_add failed" ;
    test_eq (length t2)
            1026
            "seg_sub failed" ;
    test_lst t3 
            [(seg_of 8. (pred 16.) (err_mul s1 s2 (intr_of 8. (pred 16.)))) ;
             (seg_of 16. (pred 32.) (err_mul s1 s2 (intr_of 16. (pred 32.)))) ;
             (seg_of 32. 32. (err_mul s1 s2 (intr_of 32. 32.)))]
        "seg_mul failed" ;
    test_lst t4 
            [(seg_of 1. (pred 2.) (err_div s2 s1 (intr_of 1. (pred 2.)))) ;
             (seg_of 2. (pred 4.) (err_div s2 s1 (intr_of 2. (pred 4.)))) ;
             (seg_of 4. 4. (err_div s2 s1 (intr_of 4. 4.)))]
        "seg_div failed" ;;
*)


let seg_lt_test () =
    test_bool (seg_lt s3 s1) (s3, s1) "seg_lt failed no-change test" ;
    test_bool (seg_lt s1 s4) 
              (seg_of (lower s1.int) 
                      ((upper s4.int) -. ulp (upper s4.int)) s1.err, 
               seg_of ((lower s1.int) +. ulp (lower s1.int)) 
                      (upper s4.int) s4.err)
              "seg_lt failed boundary test" ;
    test_bool (seg_lt s5 s1) 
              (seg_of (lower s5.int) 
                      ((upper s1.int) -. ulp (upper s1.int)) s5.err, s1)
              "intr_lt failed overlap test" ;; 


let seg_le_test () =
    test_bool (seg_le s3 s1) (s3, s1) "seg_le failed no-change test" ;
    test_bool (seg_le s1 s4) (seg_of (lower s1.int) (upper s4.int) s1.err,
                               seg_of (lower s1.int) (upper s4.int) s4.err)
              "seg_le failed boundary test" ;
    test_bool (seg_le s5 s1) (seg_of (lower s5.int) (upper s1.int) s5.err, s1) 
              "seg_le failed overlap test" ;; 


let seg_gt_test () =
    test_bool (seg_gt s3 s1) 
              (seg_of ((lower s1.int) +. ulp (lower s1.int)) 
                      (upper s3.int) s3.err,
               seg_of (lower s1.int) 
                      ((upper s3.int) -. ulp (upper s3.int)) s1.err)
              "range_seg failed overlap test" ;
    test_bool (seg_gt s2 s1) (s2, s1) "seg_gt failed no-change test" ;;
    test_bool (seg_gt s5 s1) 
              (seg_of ((lower s1.int) +. ulp (lower s1.int)) 
                      (upper s5.int) s5.err, s1) 
              "seg_gt failed overlap test" ;;


let seg_ge_test () =
    test_bool (seg_ge s3 s1) 
              (seg_of (lower s1.int) (upper s3.int) s3.err,
               seg_of (lower s1.int) (upper s3.int) s1.err)
              "seg_ge failed overlap test" ;
    test_bool (seg_ge s2 s1) (s2, s1) "seg_ge failed no-change test" ;;
    test_bool (seg_ge s5 s1) (seg_of (lower s1.int) (upper s5.int) s5.err, s1) 
              "seg_ge failed overlap test" ;;


let seg_eq_test () = 
    let out1 = seg_of (lower s1.int) (upper s3.int) s1.err in
    let out2 = seg_of (lower s1.int) (upper s3.int) s3.err in
    test_bool (seg_eq s1 s3) (out1, out2) "seg_eq failed test" ;;


let seg_neq_test () = 
    test_bool (seg_neq s1 s2) (s1, s2) "seg_neq test failed" ;;


let seg_without_test () =
    test_lst [ s3 ] (seg_without s3 s2) "seg_without failed no-change test" ;
    test_lst [ seg_of (lower s5.int) (pred (lower s1.int)) s5.err ; 
              seg_of (succ (upper s1.int)) (upper s5.int) s5.err ] (seg_without s5 s1) 
        "seg_without failed containing test" ;
    test_lst [ seg_of (lower s3.int) (pred (lower s1.int)) s3.err ] (seg_without s3 s1) 
        "seg_without failed overlap test" ;;


let seg_union_test () = 
    test_lst [s3 ; s2] (seg_union s3 s2) "seg_union failed no-change test" ;
    test_lst (s1 :: (seg_without s5 s1)) (seg_union s5 s1) 
        "seg_union overlap test failed" ;;


let err_tests () =
    let t1 = seg_add s1 s2 in
    let t2 = seg_sub s1 s2 in
    let t3 = seg_mul s1 s2 in
    let t4 = seg_div s2 s1 in
    test_lst (map (fun s -> err_add s1 s2 s.int) t1)
             (map (fun s -> s.err) t1)
        "err_add failed test" ;
    test_eq (map (fun s -> err_sub s1 s2 s.int) t2)
            (map (fun s -> s.err) t2)
        "err_sub failed test" ;
    test_eq (map (fun s -> err_mul s1 s2 s.int) t3)
            (map (fun s -> s.err) t3)
        "err_mul failed test" ;
    test_eq (map (fun s -> err_div s2 s1 s.int) t4)
            (map (fun s -> s.err) t4)
        "err_div failed test" ;;


let seg_testing () =
    seg_of_test () ;
    seg_overlap_test () ;
    seg_get_sterbenz_test () ;
    seg_with_test () ;
    seg_partition_test () ;
    (* seg_op_tests () ; *)
    seg_lt_test () ;
    seg_le_test () ;
    seg_gt_test () ;
    seg_ge_test () ;
    seg_eq_test () ;
    seg_neq_test () ;
    seg_without_test () ;
    seg_union_test () ;
    err_tests () ;;


(* StepFunction Testing *)
(* ---------------------- *)
let x = StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ] ;;
let y = StepF [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ] ;;
let z = StepF [ seg_of 1. 5. 0.013 ; seg_of 5. 10. 0.017 ] ;;
let t2 = StepF [ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ] ;;

let range_tests () = 
    test_eq (range x) (intr_of 2. 8.) "range failed happy path test" ;
    test_eq (range Bot) IntrBot "range failed bot test" ;
    test_eq (range_seg x) (seg_of 2. 8. 0.0) "range_seg failed happy path test" ;
    test_eq (range_seg Bot) seg_bot "range_seg failed bot test" ;;


let get_segs_test () =
    test_eq (get_segs x) [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ] 
        "get_segs happy path failed" ;
    test_eq (get_segs Bot) [] 
        "get_segs bot test failed" ;;


let append_test () = 
    let out = StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ; 
                      seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ] in
    test_sfs (sf_append x (get_segs y)) out "sf_append test failed" ;;


let limit_test () =
    let seg1 = seg_of (Float.succ 8.) (Float.pred 9.) 0.023 in
    let seg2 = seg_of 7.5 8. 0.0012 in
    let seg3 = seg_of 9. 10. 0.0043 in 
    let seg4 = seg_of (Float.succ 10.) 12. 0.0053 in
    let seg5 = seg_of (Float.succ 12.) 14. 0.1 in
    let only2 = [seg_of 7.5 12. 0.023; seg_of (Float.succ 12.) 14. 0.1] in
    let all_combined = seg_of 7.5 14. 0.1 in
    let segs1 = [seg1 ; seg2 ; seg3 ; seg4 ; seg5] in
    let adj1 = [seg2; seg3] in
    let adj2 = [seg1] in
    let adj3 = [seg1; seg4] in
    let adj4 = [seg3; seg5] in
    let adj5 = [seg4] in

    test_lst (get_adjacent_segments seg1 segs1) adj1 "get_adjacent_segments doesn't get all segments" ;
    test_lst (get_adjacent_segments seg2 segs1) adj2 "get_adjacent_segments fails with lower bound segment" ;
    test_lst (get_adjacent_segments seg5 segs1) adj5 "get_adjacent_segments fails with upper bound segment" ;

    test_eq (determine_adjacency seg1 adj1) Peak "determine_adjacency doesn't recognize a Peak" ;
    test_eq (determine_adjacency seg3 adj3) (Trough seg4) "determine_adjacency doesn't recognize a Trough" ;
    test_eq (determine_adjacency seg4 adj4) (Stair seg5) "determine_adjacency doesn't recognize a Stair" ;
    test_eq (determine_adjacency seg2 adj2) (Stair seg1) "determine_adjacency doesn't recognize a lower bound Stair" ;
    test_eq (determine_adjacency seg5 adj5) Peak "determine_adjacency doesn't recognize an upper bound Peak" ;

    test_eq (update_adjacency Peak seg1 seg2) Peak "update_adjacency erroneously updated a Peak" ;
    test_eq (update_adjacency Peak seg2 seg1) (Stair seg1) "update_adjacency did not update a Peak" ;
    test_eq (update_adjacency (Stair seg5) seg4 seg3) (Stair seg5) "update_adjacency erroneously updated a Stair" ;
    test_eq (update_adjacency (Stair seg1) seg3 seg4) (Trough seg4) "update_adjacency did not update a Stair" ;

    (* limit_merge testing *)
    let merged2 = merge_seg seg2 seg1 in
    let merged3 = merge_seg seg3 seg4 in

    test_eq (limit_merge seg1 segs1 []) None "limit_merge merged a peak" ;

    let t1 = limit_merge seg2 segs1 [] in
    (match t1 with
    | None -> failwith "limit merge failed to merge a Stair bound" 
    | Some (m, new_segs, _) -> 
        test_eq m merged2 "limit_merge failed to return the merged segment from a Stair bound" ;
        test_lst new_segs [merged2 ; seg3 ; seg4 ; seg5] 
            "limit_merge failed to update the new segments on a Stair bound properly") ;

    let t2 = limit_merge seg3 segs1 [] in
    (match t2 with
    | None -> failwith "limit merge failed to merge a Trough bound"
    | Some (m, new_segs, _) -> 
        test_eq m merged3 "limit_merge failed to return the merged segment from a Trough bound" ;
        test_lst new_segs [seg1 ; seg2 ; merged3 ; seg5] 
            "limit_merge failed to update the new segments on a Trough bound properly") ;

    (* Finally, limit testing *)
    test_lst 
        (get_segs (limit (StepF segs1) 10)) segs1 
        "limit failed on stepFunction that did not reach limit" ;

    test_lst 
        (get_segs (limit (StepF segs1) 4)) [merged2 ; seg3 ; seg4 ; seg5]
        "limit did not merge a segment" ;

    test_lst
        (get_segs (limit (StepF segs1) 2)) only2
        "limit did not merge down to 2 segments" ;

    test_lst
        (get_segs (limit (StepF segs1) 1)) [all_combined]
        "limit did not merge all segments"
;;

(* let rec limit (sf : stepF) (intervals : int) : stepF = *)



let merge_test () =
    let intervals = 1000 in
    let test = sf_append x (get_segs y) in 
    let happy_test = StepF [ seg_of 0. 1. 0.1 ; seg_of 1. 2. 0.2 ] in
    let test2 = StepF [ seg_of (-4.) 0. 0.031 ; seg_of 0. 1. 0.021 ;  
                        seg_of 1. 5. 0.021001 ; seg_of 5. 7. 0.011 ] in
    test_lst (get_segs (merge happy_test intervals))
             (get_segs happy_test)
             "merge failed no-change test" ;
    test_lst (get_segs (merge test intervals))
             ([ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ; 
               seg_of 4. 6. 0.011 ; seg_of 6. 8. 0.01 ])
             "merge failed test" ;
    test_lst (get_segs (merge test2 intervals))
             (get_segs test2)
             "merge failed boundary test" ;;


let sf_arith_tests () = 
    let intervals = 1000 in
    let x1, x2 = (seg_of 2. 4. 0.02, seg_of 4. 8. 0.01) in
    let y1, y2 = (seg_of 1. 3. 0.001, seg_of 3. 6. 0.011) in
    test_sfs 
        (eadd intervals x y) 
        (merge (StepF [seg_of 3. (pred 4.) (err_add x1 y1 (intr_of 3. (pred 4.))) ;
                       seg_of 4. 5. (err_add x1 y1 (intr_of 4. (pred 5.))) ;
                       seg_of 5. (pred 8.) (err_add x1 y2 (intr_of 5. (pred 8.))) ;
                       seg_of 8. 10. (err_add x1 y2 (intr_of 8. (pred 10.))) ;
                       seg_of 10. 14. (err_add x2 y2 (intr_of 10. 14.))]) 
               intervals) 
        "eadd failed test" ;
    test_eq (length (get_segs (esub intervals x y))) 21
        "esub failed test" ;
    test_sfs (emul intervals x y) 
        (merge (StepF [seg_of 2. (pred 4.) (err_mul x1 y1 (intr_of 2. (pred 4.))) ;
                       seg_of 4. (pred 8.) (err_mul x1 y1 (intr_of 4. (pred 8.))) ;
                       seg_of 8. 12. (err_mul x1 y1 (intr_of 8. 12.)) ;
                       seg_of 6. (pred 8.) (err_mul x1 y2 (intr_of 6. (pred 8.))) ;
                       seg_of 8. (pred 16.) (err_mul x1 y2 (intr_of 8. (pred 16.))) ;
                       seg_of 16. 24. (err_mul x1 y2 (intr_of 16. 24.)) ;
                       seg_of 4. (pred 8.) (err_mul x2 y1 (intr_of 4. (pred 8.))) ;
                       seg_of 8. (pred 16.) (err_mul x2 y1 (intr_of 8. (pred 16.))) ;
                       seg_of 16. 24. (err_mul x2 y1 (intr_of 8. 24.)) ;
                       seg_of 12. (pred 16.) (err_mul x2 y2 (intr_of 12. (pred 16.))) ;
                       seg_of 16. (pred 32.) (err_mul x2 y2 (intr_of 16. (pred 32.))) ;
                       seg_of 32. 48. (err_mul x2 y2 (intr_of 32. 48.))])
                intervals)
        "emul failed test" ;
    test_sfs (ediv intervals x y) 
        (merge (StepF [seg_of (2. /. 3.) (pred 1.)         (err_div x1 y1 (intr_of (2. /. 3.) (pred 1.))) ;
                       seg_of 1. (pred 2.)                 (err_div x1 y1 (intr_of 1. (pred 2.))) ;
                       seg_of 2. (pred 4.)                 (err_div x1 y1 (intr_of 2. (pred 4.))) ;
                       seg_of 4. 4.                        (err_div x1 y1 (intr_of 4. 4.)) ;
                       seg_of (2. /. 6.) (pred (1. /. 2.)) (err_div x1 y2 (intr_of (2. /. 6.) (pred (1. /. 2.)))) ;
                       seg_of (1. /. 2.) (pred 1.)         (err_div x1 y2 (intr_of (1. /. 2.) (pred 1.))) ;
                       seg_of 1. (4. /. 3.)                (err_div x1 y2 (intr_of 1. (4. /. 3.))) ;
                       seg_of (4. /. 3.) (pred 2.)         (err_div x2 y1 (intr_of (4. /. 3.) (pred 2.))) ;
                       seg_of 2. (pred 4.)                 (err_div x2 y1 (intr_of 2. (pred 4.))) ;
                       seg_of 4. (pred 8.)                 (err_div x2 y1 (intr_of 4. (pred 8.))) ;
                       seg_of 8. 8.                        (err_div x2 y1 (intr_of 8. 8.)) ;
                       seg_of (4. /. 6.) (pred 1.)         (err_div x2 y2 (intr_of (4. /. 6.) (pred 1.))) ;
                       seg_of 1. (pred 2.)                 (err_div x2 y2 (intr_of 1. (pred 2.))) ;
                       seg_of 2. (8. /. 3.)                (err_div x2 y2 (intr_of 2. (8. /. 3.)))])
                intervals)
        "ediv failed test" ;;


let sf_lt_test () = 
    test_sfs_b (sf_lt x y) 
               (StepF [ seg_of 2. 4. 0.02 ; seg_of 4. (6. -. ulp 6.) 0.01 ],
                StepF [ seg_of (2. +. ulp 2.) 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "sf_lt failed remove top test" ;
    test_sfs_b (sf_lt y x) 
               (StepF [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "sf_lt failed no change test" ;
    test_sfs_b (sf_lt z x) 
               (StepF [ seg_of 1. 5. 0.013 ; seg_of 5. (8. -. ulp 8.) 0.017 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "sf_lt failed contain test" ;;


let sf_le_test () = 
    test_sfs_b (sf_le x y) 
               (StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.01 ],
                StepF [ seg_of 2. 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "sf_le failed remove top test" ;
    test_sfs_b (sf_le y x) 
               (StepF [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "sf_le failed no change test" ;
    test_sfs_b (sf_le z x) 
               (StepF [ seg_of 1. 5. 0.013 ; seg_of 5. 8. 0.017 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "sf_le failed contain test" ;;


let sf_gt_test () = 
    test_sfs_b (sf_gt x y) 
               (StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ],
                StepF [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "sf_gt failed no-change top test" ;
    test_sfs_b (sf_gt y x) 
               (StepF [ seg_of (2. +. ulp 2.) 3. 0.001 ; seg_of 3. 6. 0.011 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. (6. -. ulp 6.) 0.01 ])
               "sf_gt failed remove bottom test" ;
    test_sfs_b (sf_gt z x) 
               (StepF [ seg_of (2. +. ulp 2.) 5. 0.013 ; seg_of 5. 10. 0.017 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "sf_gt failed contain test" ;;


let sf_ge_test () = 
    test_sfs_b (sf_ge x y) 
               (StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ],
                StepF [ seg_of 1. 3. 0.001 ; seg_of 3. 6. 0.011 ])
               "sf_ge failed no-change top test" ;
    test_sfs_b (sf_ge y x) 
               (StepF [ seg_of 2. 3. 0.001 ; seg_of 3. 6. 0.011 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.01 ])
               "sf_ge failed remove bottom test" ;
    test_sfs_b (sf_ge z x) 
               (StepF [ seg_of 2. 5. 0.013 ; seg_of 5. 10. 0.017 ],
                StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ])
               "sf_ge failed contain test" ;;


let sf_eq_test () = 
    test_sfs_b (sf_eq x y) 
               (StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 6. 0.01 ],
                StepF [ seg_of 2. 3. 0.001 ; seg_of 3. 6. 0.011 ]) 
               "sf_eq failed overlap test" ;
    test_sfs_b (sf_eq x z)
               (StepF [ seg_of 2. 4. 0.02 ; seg_of 4. 8. 0.01 ],
                StepF [ seg_of 2. 5. 0.013 ; seg_of 5. 8. 0.017 ]) 
               "sf_eq failed contains test" ;;
    

let sf_neq_test () = test_sfs_b (sf_neq x y) (x, y) "sf_neq failed test" ;;


let sf_union_test () =
    let intervals = 1000 in
    test_sfs (sf_union intervals x y)
             (StepF [ seg_of 1. 2. 0.001 ; seg_of 2. 4. 0.02 ;
                      seg_of 4. 6. 0.011 ; seg_of 6. 8. 0.01 ])
        "sf_union failed test" ;;


let sf_testing () =
    range_tests () ;
    get_segs_test () ;
    append_test () ;
    limit_test () ;
    merge_test () ;
    sf_arith_tests () ;
    sf_lt_test () ;
    sf_le_test () ;
    sf_gt_test () ;
    sf_ge_test () ;
    sf_eq_test () ;
    sf_neq_test () ;
    sf_union_test () ;;

(* Parser Testing *)

let test1 = 
    CCol (
        CIf (CGe (CVar ("x", FloatTyp), CVal (CInt 12)),
             CAsgn (("x", None), CAdd (CVar ("x", FloatTyp), CVal (CFloat 5.7))),
             CAsgn (("x", None), CMul (CVal (CFloat 3.1), CVar ("x", FloatTyp)))),
        CRet (CVar ("x", FloatTyp)))
    ;;

let test2 = 
    CCol (
        CCol (
            CAsgn (("x", None), CVal (CFloat 2.4)),
            CFor (CAsgn (("i", None), CVal (CInt 0)), 
                  CLt (CVar ("i", IntTyp), CVal (CInt 10)), 
                  CAsgn (("i", None), CAdd ((CVar ("i", IntTyp) , CVal (CInt 1)))),
                  CAsgn (("x", None), CAdd ((CVar ("x", FloatTyp), CVal (CFloat 2.1)))))),
        CRet (CVar ("x", FloatTyp)))
    ;;

let parser_testing () = 
    let t1 = (parse_file "c/test1.c") in 
    let t2 = (parse_file "c/test2.c") in 
    test_eq (transform t1 "foo") test1 "Parser failed test1" ;
    test_eq (transform t2 "main") test2 "Parser failed test2"  ;;

(* This is functionally the same as test2.  The difference is if the
   initialization statement of the forloop is inside the loop or just before it.
   Really just a presentation problem that seems to be intrinsic to CIL. *)
(*
let test3 = 
    CCol (
        CCol (
            CCol (CAsgn ("x", CVal (CFloat 2.4)),
                  CAsgn ("i", CVal (CInt 0))),
            CFor (CAsgn ("i", CVal (CInt 0)), 
                  CLt (CVar ("i", IntTyp), CVal (CInt 10)), 
                  CAsgn ("i", CAdd ((CVar ("i", IntTyp) , CVal (CInt 1)))),
                  CAsgn ("x", CAdd ((CVar ("x", FloatTyp), CVal (CFloat 2.1)))))),
        CRet (CVar ("x", FloatTyp)))
    ;;
*)
(* 
let failtest = 
    (* let t3 = (parse_file "c/failtest.c") in  *)
    (* test_eq (transform t3) test3 "Parser failed test3" *) ;;
*)

(* Interpreter Testing *)
(* ---------------------- *)
let runtest exp amem =
    let intervals = 1000 in
    let aexp = abst_stmt exp in
    printf "\n\n%s\n" (str_amem amem) ;
    printf "\n%s\n" (str_cstmt exp) ;
    printf "\n%s\n" (str_astmt aexp) ;
    printf "\n%s\n" (str_amem (abst_interp aexp amem intervals)) ;
    printf "------------------\n" ;;

let test = CCol (CAsgn (("x", None), CVal (CFloat 7.2)),
                 CIf (CLt (CVar ("x", FloatTyp), CVal (CFloat 12.2)),
                      CAsgn (("x", None), CAdd (CVar ("x", FloatTyp), CVal (CFloat 5.7))),
                      CAsgn (("x", None), CMul (CVal (CFloat 3.1), CVar ("x", FloatTyp))))) ;;

(* Testing with parameters *)
let amem_init = 
    let intervals = 1000 in
    amem_update intervals
                (Id "x") 
                (AFloat (StepF [{int = Intr {l = 10. ; u = 14. } ; err = 0. }]))
                amem_bot ;;

let test2 = CIf (CGt (CVar ("x", FloatTyp), CVal (CFloat 12.2)),
                 CAsgn (("x", None), CAdd (CVar ("x", FloatTyp), CVal (CFloat 5.7))),
                 CAsgn (("x", None), CMul (CVal (CFloat 3.1), CVar ("x", FloatTyp)))) ;;

(* Testing widening *)
let test3 = CFor (CAsgn (("i", None), CVal (CInt 9)),
                  CLt (CVar ("i", IntTyp), CVal (CInt 10)),
                  CAsgn (("i", None), CAdd (CVar ("i", IntTyp), CVal (CInt 1))),
                  CAsgn (("x", None), CAdd (CVar ("x", FloatTyp), CVal (CInt 1)))) ;;

let runtests () =
    (*runtest test amem_bot ;
    runtest test2 amem_init ; 
    runtest test3 amem_init ; *)
    intr_testing () ;
    seg_testing() ;
    util_testing () ;
    sf_testing () ; 
    parser_testing () ;
    Format.printf "All tests passed!\n" ;;

