include "cop.mm"
include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wa.mm"
include "opelvv.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "eqop.mm"
include "biadan2.mm"

theorem eqop2
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqop2.1: |- B e. _V
  assume eqop2.2: |- C e. _V


  assert |- ( A = <. B , C >. <-> ( A e. ( _V X. _V ) /\ ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) )

  proof
    cA
    cB
    cC
    cop
    #
    wceq
    #
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    cB
    wceq
    cA
    c2nd
    cfv
    cC
    wceq
    wa
    @1
    @3
    @0
    @2
    wcel
    cB
    cC
    eqop2.1
    eqop2.2
    opelvv
    cA
    @0
    @2
    eleq1
    mpbiri
    cA
    cB
    cC
    cvv
    cvv
    eqop
    biadan2
end
