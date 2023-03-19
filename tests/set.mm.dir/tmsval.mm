include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctmt.mm"
include "cnx.mm"
include "cts.mm"
include "cmopn.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cbs.mm"
include "cv.mm"
include "cdm.mm"
include "cds.mm"
include "cpr.mm"
include "crn.mm"
include "cuni.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-tms.mm"
include "a1i.mm"
include "wa.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "xmetf.mm"
include "fdm.mm"
include "syl.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "simpr.mm"
include "preq12d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem tmsval
  let cD: class D
  let cK: class K
  let cM: class M
  let cX: class X
  let vd: setvar d
  assume tmsval.m: |- M = { <. ( Base ` ndx ) , X >. , <. ( dist ` ndx ) , D >. }
  assume tmsval.k: |- K = ( toMetSp ` D )


  assert |- ( D e. ( *Met ` X ) -> K = ( M sSet <. ( TopSet ` ndx ) , ( MetOpen ` D ) >. ) )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    cK
    cD
    ctmt
    cfv
    cM
    cnx
    cts
    cfv
    #
    cD
    cmopn
    cfv
    #
    cop
    #
    csts
    co
    #
    tmsval.k
    @1
    vd
    cD
    cnx
    cbs
    cfv
    #
    vd
    cv
    #
    cdm
    #
    cdm
    #
    cop
    #
    cnx
    cds
    cfv
    #
    @7
    cop
    #
    cpr
    #
    @2
    @7
    cmopn
    cfv
    #
    cop
    #
    csts
    co
    #
    @5
    cxmt
    crn
    cuni
    #
    ctmt
    cvv
    ctmt
    vd
    @17
    @16
    cmpt
    wceq
    @1
    vd
    df-tms
    a1i
    @1
    @7
    cD
    wceq
    #
    wa
    #
    @13
    cM
    @15
    @4
    csts
    @19
    @13
    @6
    cX
    cop
    #
    @11
    cD
    cop
    #
    cpr
    cM
    @19
    @10
    @20
    @12
    @21
    @19
    @9
    cX
    @6
    @18
    @1
    @9
    cD
    cdm
    #
    cdm
    #
    cX
    @18
    @8
    @22
    @7
    cD
    dmeq
    dmeqd
    @1
    @23
    cX
    cX
    cxp
    #
    cdm
    cX
    @1
    @22
    @24
    @1
    @24
    cxr
    cD
    wf
    @22
    @24
    wceq
    cD
    cX
    xmetf
    @24
    cxr
    cD
    fdm
    syl
    dmeqd
    cX
    dmxpid
    syl6eq
    sylan9eqr
    opeq2d
    @19
    @7
    cD
    @11
    @1
    @18
    simpr
    #
    opeq2d
    preq12d
    tmsval.m
    syl6eqr
    @19
    @14
    @3
    @2
    @19
    @7
    cD
    cmopn
    @25
    fveq2d
    opeq2d
    oveq12d
    @0
    @17
    cD
    cxmt
    cX
    fvssunirn
    sseli
    @1
    cM
    @4
    csts
    ovexd
    fvmptd
    syl5eq
end
