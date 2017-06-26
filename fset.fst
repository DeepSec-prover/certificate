module Fset

assume type fset (a:eqtype)
assume type equal (#a:eqtype) (s1:fset a) (s2:fset a)

(* destructors *)

assume val mem : #a:eqtype -> a -> fset a -> Tot bool

(* constructors *)
assume val fempty      : #a:eqtype -> Tot (fset a)
assume val fsingleton  : #a:eqtype -> a -> Tot (fset a)
assume val funion      : #a:eqtype -> fset a -> fset a -> Tot (fset a)
assume val fintersect  : #a:eqtype -> fset a -> fset a -> Tot (fset a)
assume val fcomplement : #a:eqtype -> fset a -> Tot (fset a)

(* ops *)
assume type fsubset (#a:eqtype) (s1:fset a) (s2:fset a) :Type0

(* Properties *)
assume val mem_fempty: #a:eqtype -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x fempty)))
   [SMTPat (mem x fempty)]

assume val mem_fsingleton: #a:eqtype -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (fsingleton x) = (x=y)))
   [SMTPat (mem y (fsingleton x))]

assume val mem_funion: #a:eqtype -> x:a -> s1:fset a -> s2:fset a -> Lemma
   (requires True)
   (ensures (mem x (funion s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (funion s1 s2))]

assume val mem_fintersect: #a:eqtype -> x:a -> s1:fset a -> s2:fset a -> Lemma
   (requires True)
   (ensures (mem x (fintersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (fintersect s1 s2))]

assume val mem_fcomplement: #a:eqtype -> x:a -> s:fset a -> Lemma
   (requires True)
   (ensures (mem x (fcomplement s) = not (mem x s)))
   [SMTPat (mem x (fcomplement s))]

assume val mem_subset: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (fsubset s1 s2))
   [SMTPat (fsubset s1 s2)]

assume val subset_mem: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
   (requires (fsubset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (fsubset s1 s2)]

assume val lemma_union_empty : #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
  (requires (equal s2 fempty))
  (ensures (equal s1 (funion s1 s2)))
  [SMTPat (funion s1 s2)]

assume val lemma_union_id : #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
  (requires (equal s1 s2))
  (ensures (equal (funion s1 s2) s1))
  [SMTPat (funion s1 s2)]

assume val lemma_union_subset1 : #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
  (requires True)
  (ensures fsubset s2 (funion s1 s2))
  [SMTPat (fsubset s2 (funion s1 s2))]

assume val lemma_union_subset2 : #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
  (requires True)
  (ensures fsubset s2 (funion s1 s2))
  [SMTPat (fsubset s2 (funion s2 s1))]

assume val lemma_union_comm : #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
  (requires True)
  (ensures (equal (funion s1 s2) (funion s2 s1)))
  [SMTPat (funion s1 s2)]

assume val lemma_union_assoc : #a:eqtype -> s1:fset a -> s2:fset a -> s3:fset a -> Lemma
  (requires True)
  (ensures (equal (funion s1 (funion s2 s3)) (funion s2 (funion s1 s3))))
  [SMTPat (funion s1 (funion s2 s3))]

(* extensionality *)

assume val lemma_equal_intro: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPatT (equal s1 s2)]

assume val lemma_equal_elim: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPatT (equal s1 s2)]

assume val lemma_equal_refl: #a:eqtype -> s1:fset a -> s2:fset a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPatT (equal s1 s2)]

assume val size : #a:eqtype -> s:fset a -> Tot nat

assume val size_lemma : #a:eqtype -> x:a -> s1:fset a -> s2:fset a -> Lemma (requires ((fsubset s1 s2) /\ (mem x s2) /\ not(mem x s1)) ) (ensures size s1 < size s2)
