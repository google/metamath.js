include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wa.mm"
include "cuni.mm"
include "elxp7.mm"
include "elvvuni.mm"
include "adantr.mm"
include "cv.mm"
include "cab.mm"
include "wex.mm"
include "simprl.mm"
include "wceq.mm"
include "eleq2.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpcom.mm"
include "eluniab.mm"
include "sylibr.mm"
include "crab.mm"
include "xp2.mm"
include "df-rab.mm"
include "eqtri.mm"
include "unieqi.mm"
include "syl6eleqr.mm"
include "mpancom.mm"
include "sylbi.mm"

theorem unielxp
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. ( B X. C ) -> U. A e. U. ( B X. C ) )

  proof
    cA
    cB
    cC
    cxp
    #
    wcel
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
    #
    cB
    wcel
    #
    cA
    c2nd
    cfv
    #
    cC
    wcel
    #
    wa
    #
    wa
    #
    cA
    cuni
    #
    @0
    cuni
    #
    wcel
    #
    cA
    cB
    cC
    elxp7
    @9
    cA
    wcel
    #
    @8
    @11
    @2
    @12
    @7
    cA
    elvvuni
    adantr
    @12
    @8
    wa
    #
    @9
    vx
    cv
    #
    @1
    wcel
    #
    @14
    c1st
    cfv
    #
    cB
    wcel
    #
    @14
    c2nd
    cfv
    #
    cC
    wcel
    #
    wa
    #
    wa
    #
    vx
    cab
    #
    cuni
    #
    @10
    @13
    @9
    @14
    wcel
    #
    @21
    wa
    #
    vx
    wex
    #
    @9
    @23
    wcel
    @2
    @13
    @26
    @12
    @2
    @7
    simprl
    @25
    @13
    vx
    cA
    @1
    @14
    cA
    wceq
    #
    @24
    @12
    @21
    @8
    @14
    cA
    @9
    eleq2
    @27
    @15
    @2
    @20
    @7
    @14
    cA
    @1
    eleq1
    @27
    @17
    @4
    @19
    @6
    @27
    @16
    @3
    cB
    @14
    cA
    c1st
    fveq2
    eleq1d
    @27
    @18
    @5
    cC
    @14
    cA
    c2nd
    fveq2
    eleq1d
    anbi12d
    anbi12d
    anbi12d
    spcegv
    mpcom
    @21
    vx
    @9
    eluniab
    sylibr
    @0
    @22
    @0
    @20
    vx
    @1
    crab
    @22
    vx
    cB
    cC
    xp2
    @20
    vx
    @1
    df-rab
    eqtri
    unieqi
    syl6eleqr
    mpancom
    sylbi
end
