include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "metustss.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"

theorem metustrel
  let cA: class A
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint A a
  disjoint F a
  disjoint B a
  disjoint a b
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  assert |- ( ( D e. ( PsMet ` X ) /\ A e. F ) -> Rel A )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    cA
    cF
    wcel
    wa
    #
    cA
    cvv
    cvv
    cxp
    #
    wss
    cA
    wrel
    @0
    cA
    cX
    cX
    cxp
    @1
    cA
    cD
    cF
    cX
    va
    metust.1
    metustss
    cX
    cX
    xpss
    syl6ss
    cA
    df-rel
    sylibr
end
