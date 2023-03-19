include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cxp.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "cuni.mm"
include "cmetu.mm"
include "cvv.mm"
include "wceq.mm"
include "df-metu.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "dmeqd.mm"
include "psmetdmdm.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "sqxpeqd.mm"
include "simplr.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "oveq12d.mm"
include "wrex.mm"
include "elfvdm.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "mpancom.mm"
include "wfun.mm"
include "wb.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cxr.mm"
include "cmap.mm"
include "crab.mm"
include "df-psmet.mm"
include "funmpt2.mm"
include "elunirn.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem metuval
  let cD: class D
  let cX: class X
  let va: setvar a
  let vd: setvar d
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint D a
  disjoint X a
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a d
  disjoint a x
  disjoint D d
  disjoint D x
  disjoint X d
  disjoint X x
  assert |- ( D e. ( PsMet ` X ) -> ( metUnif ` D ) = ( ( X X. X ) filGen ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) ) ) )

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
    vd
    cv
    #
    cdm
    #
    cdm
    #
    @4
    cxp
    #
    va
    crp
    @2
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cX
    cX
    cxp
    #
    va
    crp
    cD
    ccnv
    #
    @8
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    cpsmet
    crn
    cuni
    #
    cmetu
    cvv
    cmetu
    vd
    @18
    @12
    cmpt
    wceq
    @1
    va
    vd
    df-metu
    a1i
    @1
    @2
    cD
    wceq
    #
    wa
    #
    @5
    @13
    @11
    @17
    cfg
    @20
    @4
    cX
    @20
    @4
    cD
    cdm
    #
    cdm
    #
    cX
    @20
    @3
    @21
    @20
    @2
    cD
    @1
    @19
    simpr
    dmeqd
    dmeqd
    @1
    cX
    @22
    wceq
    @19
    cD
    cX
    psmetdmdm
    adantr
    eqtr4d
    sqxpeqd
    @20
    @10
    @16
    @20
    va
    crp
    @9
    @15
    @20
    @7
    crp
    wcel
    #
    wa
    #
    @6
    @14
    @8
    @24
    @2
    cD
    @1
    @19
    @23
    simplr
    cnveqd
    imaeq1d
    mpteq2dva
    rneqd
    oveq12d
    @1
    cD
    vx
    cv
    #
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
    @18
    wcel
    #
    cX
    @28
    wcel
    @1
    @29
    cD
    cX
    cpsmet
    elfvdm
    @27
    @1
    vx
    cX
    @28
    @25
    cX
    wceq
    @26
    @0
    cD
    @25
    cX
    cpsmet
    fveq2
    eleq2d
    rspcev
    mpancom
    cpsmet
    wfun
    @30
    @29
    wb
    vy
    cvv
    vz
    cv
    #
    @31
    vu
    cv
    #
    co
    cc0
    wceq
    @31
    vw
    cv
    #
    @32
    co
    vv
    cv
    #
    @31
    @32
    co
    @34
    @33
    @32
    co
    cxad
    co
    cle
    wbr
    vv
    vy
    cv
    #
    wral
    vw
    @35
    wral
    wa
    vz
    @35
    wral
    vu
    cxr
    @35
    @35
    cxp
    cmap
    co
    crab
    cpsmet
    vy
    vz
    vw
    vv
    vu
    df-psmet
    funmpt2
    vx
    cD
    cpsmet
    elunirn
    ax-mp
    sylibr
    @1
    @13
    @17
    cfg
    ovexd
    fvmptd
end
