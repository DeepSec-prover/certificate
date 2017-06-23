module Fset

open FStar.FunctionalExtensionality

abstract type fset (a:eqtype) = a -> Tot bool
abstract type equal (#a:eqtype) (s1:fset a) (s2:fset a) = feq s1 s2

(* destructors *)

abstract val mem : #a:eqtype -> a -> fset a -> Tot bool
let mem #a x s = s x

(* constructors *)
abstract val fempty      : #a:eqtype -> Tot (fset a)
abstract val fsingleton  : #a:eqtype -> a -> Tot (fset a)
abstract val funion      : #a:eqtype -> fset a -> fset a -> Tot (fset a)
abstract val fintersect  : #a:eqtype -> fset a -> fset a -> Tot (fset a)
abstract val fcomplement : #a:eqtype -> fset a -> Tot (fset a)

let fempty              = fun #a x -> false
let fsingleton #a x     = fun y -> y = x
let funion #a s1 s2     = fun x -> s1 x || s2 x
let fintersect #a s1 s2 = fun x -> s1 x && s2 x
let fcomplement #a s    = fun x -> not (s x)

(* ops *)
type fsubset (#a:eqtype) (s1:fset a) (s2:fset a) :Type0 = forall x. mem x s1 ==> mem x s2

(* Properties *)
abstract val mem_empty: #a:eqtype -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x fempty)))
   [SMTPat (mem x fempty)]

abstract val mem_fsingleton: #a:eqtype -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (fsingleton x) = (x=y)))
   [SMTPat (mem y (fsingleton x))]

abstract val mem_funion: #a:eqtype -> x:a -> s1:fset a -> s2:fset a -> Lemma
   (requires True)
   (ensures (mem x (funion s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (funion s1 s2))]

abstract val mem_fintersect: #a:eqtype -> x:a -> s1:fset a -> s2:fset a -> Lemma
   (requires True)
   (ensures (mem x (fintersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (fintersect s1 s2))]

abstract val mem_fcomplement: #a:eqtype -> x:a -> s:fset a -> Lemma
   (requires True)
   (ensures (mem x (fcomplement s) = not (mem x s)))
   [SMTPat (mem x (fcomplement s))]

abstract val mem_subset: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (fsubset s1 s2))
   [SMTPat (fsubset s1 s2)]

abstract val subset_mem: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
   (requires (fsubset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (fsubset s1 s2)]

let mem_empty      #a x       = ()
let mem_fsingleton  #a x y     = ()
let mem_funion      #a x s1 s2 = ()
let mem_fintersect  #a x s1 s2 = ()
let mem_fcomplement #a x s     = ()
let subset_mem     #a s1 s2   = ()
let mem_fsubset     #a s1 s2   = ()

(* extensionality *)

abstract val lemma_equal_intro: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPatT (equal s1 s2)]

abstract val lemma_equal_elim: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPatT (equal s1 s2)]

abstract val lemma_equal_refl: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPatT (equal s1 s2)]

  let lemma_equal_intro #a s1 s2 = ()
  let lemma_equal_elim  #a s1 s2 = ()
  let lemma_equal_refl  #a s1 s2 = ()


(*abstract val size : #a:eqtype -> s:fset a -> Tot nat

abstract val size_lemma : #a:eqtype -> s1:fset a -> s2:fset a -> x:a -> Lemma (requires ((fsubset s1 s2) && (mem x s2) && not(mem x s1)) ) (ensures size s1 < size s2)*)
