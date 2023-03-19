include "cxp.mm"
include "wcel.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "crn.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "elxp4.mm"
include "1stval.mm"
include "2ndval.mm"
include "opeq12i.mm"
include "eqeq2i.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "bitr4i.mm"

theorem elxp6
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B X. C ) <-> ( A = <. ( 1st ` A ) , ( 2nd ` A ) >. /\ ( ( 1st ` A ) e. B /\ ( 2nd ` A ) e. C ) ) )

  proof
    cA
    cB
    cC
    cxp
    wcel
    cA
    cA
    csn
    #
    cdm
    cuni
    #
    @0
    crn
    cuni
    #
    cop
    #
    wceq
    #
    @1
    cB
    wcel
    #
    @2
    cC
    wcel
    #
    wa
    #
    wa
    cA
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @8
    cB
    wcel
    #
    @9
    cC
    wcel
    #
    wa
    #
    wa
    cA
    cB
    cC
    elxp4
    @11
    @4
    @14
    @7
    @10
    @3
    cA
    @8
    @1
    @9
    @2
    cA
    1stval
    #
    cA
    2ndval
    #
    opeq12i
    eqeq2i
    @12
    @5
    @13
    @6
    @8
    @1
    cB
    @15
    eleq1i
    @9
    @2
    cC
    @16
    eleq1i
    anbi12i
    anbi12i
    bitr4i
end
