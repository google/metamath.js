include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "crn.mm"
include "cdm.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "cvv.mm"
include "csumge0.mm"
include "wceq.mm"
include "df-sumge0.mm"
include "a1i.mm"
include "wb.mm"
include "rneq.mm"
include "eleq2d.mm"
include "adantl.mm"
include "dmeq.mm"
include "fdm.mm"
include "adantr.mm"
include "eqtrd.mm"
include "pweqd.mm"
include "ineq1d.mm"
include "mpteq1d.mm"
include "adantll.mm"
include "fveq1.mm"
include "sumeq2ad.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "ifbieq2d.mm"
include "simpr.mm"
include "simpl.mm"
include "fex.mm"
include "syl2anc.mm"
include "pnfxr.mm"
include "xrltso.mm"
include "supex.mm"
include "ifexg.mm"
include "fvmptd.mm"

theorem sge0val
  let vy: setvar y
  let vw: setvar w
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vk: setvar k

  disjoint F w
  disjoint F y
  disjoint w y
  disjoint X y
  disjoint F x
  disjoint w x
  disjoint x y
  disjoint V x
  disjoint X x
  disjoint k x
  assert |- ( ( X e. V /\ F : X --> ( 0 [,] +oo ) ) -> ( sum^ ` F ) = if ( +oo e. ran F , +oo , sup ( ran ( y e. ( ~P X i^i Fin ) |-> sum_ w e. y ( F ` w ) ) , RR* , < ) ) )

  proof
    cX
    cV
    wcel
    #
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    wa
    #
    vx
    cF
    cpnf
    vx
    cv
    #
    crn
    #
    wcel
    #
    cpnf
    vy
    @4
    cdm
    #
    cpw
    #
    cfn
    cin
    #
    vy
    cv
    #
    vw
    cv
    #
    @4
    cfv
    #
    vw
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cif
    #
    cpnf
    cF
    crn
    #
    wcel
    #
    cpnf
    vy
    cX
    cpw
    #
    cfn
    cin
    #
    @10
    @11
    cF
    cfv
    #
    vw
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cif
    #
    cvv
    csumge0
    cvv
    csumge0
    vx
    cvv
    @17
    cmpt
    wceq
    @3
    vx
    vy
    vw
    df-sumge0
    a1i
    @3
    @4
    cF
    wceq
    #
    wa
    #
    @6
    @19
    @16
    @26
    cpnf
    @28
    @6
    @19
    wb
    @3
    @28
    @5
    @18
    cpnf
    @4
    cF
    rneq
    eleq2d
    adantl
    @29
    cxr
    @15
    @25
    clt
    @29
    @14
    @24
    @29
    @14
    vy
    @21
    @13
    cmpt
    #
    @24
    @2
    @28
    @14
    @30
    wceq
    @0
    @2
    @28
    wa
    #
    vy
    @9
    @21
    @13
    @31
    @8
    @20
    cfn
    @31
    @7
    cX
    @31
    @7
    cF
    cdm
    #
    cX
    @28
    @7
    @32
    wceq
    @2
    @4
    cF
    dmeq
    adantl
    @2
    @32
    cX
    wceq
    @28
    cX
    @1
    cF
    fdm
    adantr
    eqtrd
    pweqd
    ineq1d
    mpteq1d
    adantll
    @28
    @30
    @24
    wceq
    @3
    @28
    vy
    @21
    @13
    @23
    @28
    @10
    @12
    @22
    vw
    @11
    @4
    cF
    fveq1
    sumeq2ad
    mpteq2dv
    adantl
    eqtrd
    rneqd
    supeq1d
    ifbieq2d
    @3
    @2
    @0
    cF
    cvv
    wcel
    @0
    @2
    simpr
    @0
    @2
    simpl
    cX
    @1
    cV
    cF
    fex
    syl2anc
    @3
    cpnf
    cxr
    wcel
    #
    @26
    cvv
    wcel
    #
    @27
    cvv
    wcel
    @33
    @3
    pnfxr
    a1i
    @34
    @3
    cxr
    @25
    clt
    xrltso
    supex
    a1i
    @19
    cpnf
    @26
    cxr
    cvv
    ifexg
    syl2anc
    fvmptd
end
