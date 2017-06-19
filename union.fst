module Union

open FStar.Set

val union_lemma1 : #a:eqtype -> s1:set a -> s2:set a -> Lemma
(requires (subset s1 s2))
(ensures (equal (union s1 s2) s2)) [SMTPat (FStar.Set.union s1 s2)]

let rec union_lemma1 #a s1 s2 = ()

val union_lemma2 : #a :eqtype -> s1:set a -> s2:set a -> s3:set a -> Lemma (requires true)( ensures (equal (union s1 (union s2 s3)) (union s2 (union s1 s3))) ) [SMTPat (FStar.Set.union s1 (union s2 s3))]

let union_lemma2 #a s1 s2 s3 = ()

val union_lemma3 : #a:eqtype -> s1:set a -> s2:set a -> Lemma (requires true) (ensures (equal (union s1 s2) (union s2 s1))) [SMTPat (FStar.Set.union s1 s2)]

let rec union_lemma3 #a s1 s2 = ()

val union_lemma4 : #a:eqtype -> s1:set a -> s2:set a -> Lemma (requires true) (ensures ( (equal s1 s2) ==> (equal s1 (union s1 s2)) )) [SMTPat (FStar.Set.union s1 s2)]

let union_lemma4 #a s1 s2 = ()
