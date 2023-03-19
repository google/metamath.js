include "cop.mm"
include "cid.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "wa.mm"
include "bj-elid.mm"
include "opelxp.mm"
include "anbi1i.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "eqeq12d.mm"
include "pm5.32i.mm"
include "simpl.mm"
include "anim1i.mm"
include "eleq1.mm"
include "biimpac.mm"
include "simpr.mm"
include "jca31.mm"
include "impbii.mm"
include "bitri.mm"

theorem bj-elid3
  let cA: class A
  let cB: class B


  assert |- ( <. A , B >. e. _I <-> ( A e. _V /\ A = B ) )

  proof
    cA
    cB
    cop
    #
    cid
    wcel
    @0
    cvv
    cvv
    cxp
    wcel
    #
    @0
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    wceq
    #
    wa
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    wceq
    #
    wa
    #
    @0
    bj-elid
    @5
    @6
    cB
    cvv
    wcel
    #
    wa
    #
    @4
    wa
    #
    @8
    @1
    @10
    @4
    cA
    cB
    cvv
    cvv
    opelxp
    anbi1i
    @11
    @10
    @7
    wa
    #
    @8
    @10
    @4
    @7
    @10
    @2
    cA
    @3
    cB
    cA
    cB
    cvv
    cvv
    op1stg
    cA
    cB
    cvv
    cvv
    op2ndg
    eqeq12d
    pm5.32i
    @12
    @8
    @10
    @6
    @7
    @6
    @9
    simpl
    anim1i
    @8
    @6
    @9
    @7
    @6
    @7
    simpl
    @7
    @6
    @9
    cA
    cB
    cvv
    eleq1
    biimpac
    @6
    @7
    simpr
    jca31
    impbii
    bitri
    bitri
    bitri
end
