include "ccat.mm"
include "wcel.mm"
include "ciso.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "wfn.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cmpt.mm"
include "cinv.mm"
include "ccom.mm"
include "crn.mm"
include "wss.mm"
include "wral.mm"
include "dmexg.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "csect.mm"
include "co.mm"
include "ccnv.mm"
include "cin.mm"
include "cmpt2.mm"
include "wa.mm"
include "ovex.mm"
include "inex1.mm"
include "a1i.mm"
include "ralrimivva.mm"
include "fnmpt2.mm"
include "wceq.mm"
include "df-inv.mm"
include "fveq2.mm"
include "oveqd.mm"
include "cnveqd.mm"
include "ineq12d.mm"
include "mpt2eq123dv.mm"
include "id.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "mpt2exg.mm"
include "mp1i.mm"
include "fvmptd.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "ssv.mm"
include "fnco.mm"
include "syl3anc.mm"
include "isofval.mm"

theorem isofn
  let cC: class C
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y


  assert |- ( C e. Cat -> ( Iso ` C ) Fn ( ( Base ` C ) X. ( Base ` C ) ) )

  proof
    cC
    ccat
    wcel
    #
    cC
    ciso
    cfv
    #
    cC
    cbs
    cfv
    #
    @2
    cxp
    #
    wfn
    vx
    cvv
    vx
    cv
    #
    cdm
    #
    cmpt
    #
    cC
    cinv
    cfv
    #
    ccom
    #
    @3
    wfn
    #
    @0
    @6
    cvv
    wfn
    #
    @7
    @3
    wfn
    #
    @7
    crn
    #
    cvv
    wss
    #
    @9
    @0
    @5
    cvv
    wcel
    #
    vx
    cvv
    wral
    @10
    @0
    @14
    vx
    cvv
    @4
    cvv
    wcel
    @14
    @0
    @4
    cvv
    dmexg
    adantl
    ralrimiva
    vx
    cvv
    @5
    @6
    cvv
    @6
    eqid
    fnmpt
    syl
    @0
    @11
    vx
    vy
    @2
    @2
    @4
    vy
    cv
    #
    cC
    csect
    cfv
    #
    co
    #
    @15
    @4
    @16
    co
    #
    ccnv
    #
    cin
    #
    cmpt2
    #
    @3
    wfn
    #
    @0
    @20
    cvv
    wcel
    #
    vy
    @2
    wral
    vx
    @2
    wral
    @22
    @0
    @23
    vx
    vy
    @2
    @2
    @23
    @0
    @4
    @2
    wcel
    @15
    @2
    wcel
    wa
    wa
    @17
    @19
    @4
    @15
    @16
    ovex
    inex1
    a1i
    ralrimivva
    vx
    vy
    @2
    @2
    @20
    @21
    cvv
    @21
    eqid
    #
    fnmpt2
    syl
    @0
    @3
    @7
    @21
    @0
    vc
    cC
    vx
    vy
    vc
    cv
    #
    cbs
    cfv
    #
    @26
    @4
    @15
    @25
    csect
    cfv
    #
    co
    #
    @15
    @4
    @27
    co
    #
    ccnv
    #
    cin
    #
    cmpt2
    #
    @21
    ccat
    cinv
    cvv
    cinv
    vc
    ccat
    @32
    cmpt
    wceq
    @0
    vx
    vy
    vc
    df-inv
    a1i
    @25
    cC
    wceq
    #
    @32
    @21
    wceq
    @0
    @33
    vx
    vy
    @26
    @26
    @31
    @2
    @2
    @20
    @25
    cC
    cbs
    fveq2
    #
    @34
    @33
    @28
    @17
    @30
    @19
    @33
    @27
    @16
    @4
    @15
    @25
    cC
    csect
    fveq2
    #
    oveqd
    @33
    @29
    @18
    @33
    @27
    @16
    @15
    @4
    @35
    oveqd
    cnveqd
    ineq12d
    mpt2eq123dv
    adantl
    @0
    id
    @2
    cvv
    wcel
    #
    @36
    wa
    @21
    cvv
    wcel
    @0
    @36
    @36
    cC
    cbs
    fvex
    #
    @37
    pm3.2i
    vx
    vy
    @2
    @2
    @20
    cvv
    cvv
    @21
    @24
    mpt2exg
    mp1i
    fvmptd
    fneq1d
    mpbird
    @13
    @0
    @12
    ssv
    a1i
    cvv
    @3
    @6
    @7
    fnco
    syl3anc
    @0
    @3
    @1
    @8
    vx
    cC
    isofval
    fneq1d
    mpbird
end
