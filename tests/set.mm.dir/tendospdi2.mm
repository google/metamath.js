include "tendopl2.mm"

theorem tendospdi2
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  assume tendospd.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendosp.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint f s
  disjoint f t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint W f
  disjoint W s
  disjoint W t
  assert |- ( ( U e. E /\ V e. E /\ F e. T ) -> ( ( U P V ) ` F ) = ( ( U ` F ) o. ( V ` F ) ) )

  proof
    vt
    cP
    cT
    cU
    vf
    cE
    cF
    cK
    cV
    cW
    vs
    tendosp.p
    tendospd.t
    tendopl2
end
