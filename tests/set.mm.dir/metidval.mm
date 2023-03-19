include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "copab.mm"
include "crn.mm"
include "cuni.mm"
include "cmetid.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-metid.mm"
include "a1i.mm"
include "simpr.mm"
include "dmeqd.mm"
include "psmetdmdm.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "opabbidv.mm"
include "wrex.mm"
include "elfvdm.mm"
include "fveq2.mm"
include "rspcev.mm"
include "mpancom.mm"
include "wfun.mm"
include "wb.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cxr.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "df-psmet.mm"
include "funmpt2.mm"
include "elunirn.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wss.mm"
include "opabssxp.mm"
include "elfvex.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "sylancr.mm"
include "fvmptd.mm"

theorem metidval
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cX: class X
  let vd: setvar d
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint X x
  disjoint X y
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint D d
  disjoint X d
  assert |- ( D e. ( PsMet ` X ) -> ( ~Met ` D ) = { <. x , y >. | ( ( x e. X /\ y e. X ) /\ ( x D y ) = 0 ) } )

  proof
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    vd
    cD
    vx
    cv
    #
    vd
    cv
    #
    cdm
    #
    cdm
    #
    wcel
    #
    vy
    cv
    #
    @5
    wcel
    #
    wa
    #
    @2
    @7
    @3
    co
    #
    cc0
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @2
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    wa
    #
    @2
    @7
    cD
    co
    #
    cc0
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    cpsmet
    crn
    cuni
    #
    cmetid
    cvv
    cmetid
    vd
    @21
    @13
    cmpt
    wceq
    @1
    vx
    vy
    vd
    df-metid
    a1i
    @1
    @3
    cD
    wceq
    #
    wa
    #
    @12
    @19
    vx
    vy
    @23
    @9
    @16
    @11
    @18
    @23
    @6
    @14
    @8
    @15
    @23
    @5
    cX
    @2
    @23
    @5
    cD
    cdm
    #
    cdm
    #
    cX
    @23
    @4
    @24
    @23
    @3
    cD
    @1
    @22
    simpr
    #
    dmeqd
    dmeqd
    @1
    cX
    @25
    wceq
    @22
    cD
    cX
    psmetdmdm
    adantr
    eqtr4d
    #
    eleq2d
    @23
    @5
    cX
    @7
    @27
    eleq2d
    anbi12d
    @23
    @10
    @17
    cc0
    @23
    @3
    cD
    @2
    @7
    @26
    oveqd
    eqeq1d
    anbi12d
    opabbidv
    @1
    cD
    @2
    cpsmet
    cfv
    #
    wcel
    #
    vx
    cpsmet
    cdm
    #
    wrex
    #
    cD
    @21
    wcel
    #
    cX
    @30
    wcel
    @1
    @31
    cD
    cX
    cpsmet
    elfvdm
    @29
    @1
    vx
    cX
    @30
    @2
    cX
    wceq
    @28
    @0
    cD
    @2
    cX
    cpsmet
    fveq2
    eleq2d
    rspcev
    mpancom
    cpsmet
    wfun
    @32
    @31
    wb
    vx
    cvv
    @7
    @7
    @3
    co
    cc0
    wceq
    @7
    vz
    cv
    #
    @3
    co
    vw
    cv
    #
    @7
    @3
    co
    @34
    @33
    @3
    co
    cxad
    co
    cle
    wbr
    vw
    @2
    wral
    vz
    @2
    wral
    wa
    vy
    @2
    wral
    vd
    cxr
    @2
    @2
    cxp
    cmap
    co
    crab
    cpsmet
    vx
    vy
    vz
    vw
    vd
    df-psmet
    funmpt2
    vx
    cD
    cpsmet
    elunirn
    ax-mp
    sylibr
    @1
    @20
    cX
    cX
    cxp
    #
    wss
    @35
    cvv
    wcel
    #
    @20
    cvv
    wcel
    @18
    vx
    vy
    cX
    cX
    opabssxp
    @1
    cX
    cvv
    wcel
    #
    @37
    @36
    cD
    cX
    cpsmet
    elfvex
    #
    @38
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    @20
    @35
    cvv
    ssexg
    sylancr
    fvmptd
end
