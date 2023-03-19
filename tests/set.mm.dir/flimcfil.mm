include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cflim.mm"
include "co.mm"
include "wa.mm"
include "ccfil.mm"
include "cfil.mm"
include "cv.mm"
include "cbl.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cuni.mm"
include "eqid.mm"
include "flimfil.mm"
include "adantl.mm"
include "wceq.mm"
include "mopnuni.mm"
include "adantr.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "flimelbas.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "csn.mm"
include "cnei.mm"
include "simplr.mm"
include "ctop.mm"
include "mopntop.mm"
include "cxr.mm"
include "simpll.mm"
include "rpxr.mm"
include "blopn.mm"
include "syl3anc.mm"
include "simpr.mm"
include "blcntr.mm"
include "opnneip.mm"
include "flimnei.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "wb.mm"
include "iscfil3.mm"
include "mpbir2and.mm"

theorem flimcfil
  let cA: class A
  let cD: class D
  let cF: class F
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vj: setvar j
  let vu: setvar u
  assume lmcau.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( *Met ` X ) /\ A e. ( J fLim F ) ) -> F e. ( CauFil ` D ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    wa
    #
    cF
    cD
    ccfil
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    cF
    wcel
    #
    vy
    cX
    wrex
    #
    vx
    crp
    wral
    #
    @2
    cF
    cJ
    cuni
    #
    cfil
    cfv
    #
    @4
    @1
    cF
    @14
    wcel
    @0
    cA
    cF
    cJ
    @13
    @13
    eqid
    #
    flimfil
    adantl
    @2
    cX
    @13
    cfil
    @0
    cX
    @13
    wceq
    #
    @1
    cD
    cJ
    cX
    lmcau.1
    mopnuni
    #
    adantr
    fveq2d
    eleqtrrd
    @2
    @11
    vx
    crp
    @2
    @7
    crp
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cA
    @7
    @8
    co
    #
    cF
    wcel
    #
    @11
    @19
    cA
    @13
    cX
    @1
    cA
    @13
    wcel
    @0
    @18
    cA
    cF
    cJ
    @13
    @15
    flimelbas
    ad2antlr
    @0
    @16
    @1
    @18
    @17
    ad2antrr
    eleqtrrd
    #
    @19
    @1
    @21
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    @22
    @0
    @1
    @18
    simplr
    @19
    cJ
    ctop
    wcel
    #
    @21
    cJ
    wcel
    #
    cA
    @21
    wcel
    #
    @24
    @0
    @25
    @1
    @18
    cD
    cJ
    cX
    lmcau.1
    mopntop
    ad2antrr
    @19
    @0
    @20
    @7
    cxr
    wcel
    #
    @26
    @0
    @1
    @18
    simpll
    #
    @23
    @18
    @28
    @2
    @7
    rpxr
    adantl
    cD
    cA
    @7
    cJ
    cX
    lmcau.1
    blopn
    syl3anc
    @19
    @0
    @20
    @18
    @27
    @29
    @23
    @2
    @18
    simpr
    cD
    cA
    @7
    cX
    blcntr
    syl3anc
    cA
    cJ
    @21
    opnneip
    syl3anc
    cA
    cF
    cJ
    @21
    flimnei
    syl2anc
    @10
    @22
    vy
    cA
    cX
    @6
    cA
    wceq
    @9
    @21
    cF
    @6
    cA
    @7
    @8
    oveq1
    eleq1d
    rspcev
    syl2anc
    ralrimiva
    @0
    @3
    @5
    @12
    wa
    wb
    @1
    vy
    cD
    cF
    cX
    vx
    iscfil3
    adantr
    mpbir2and
end
