module Union

open FStar.Set

val union_lemma1 : #a:eqtype -> l1:set a -> l2:set a -> Lemma
(requires (subset l1 l2))
(ensures (union l1 l2 = l2)) [SMTPat (union l1 l2)]

let rec union_lemma1 #a l1 l2 = ()

(*val union_lemma2 : #a:eqtype -> l1:list a -> l2:list a -> Lemma (requires true) (ensures (union l1 l2 = union l2 l1))

let rec union_lemma2 #a l1 l2 =*)
