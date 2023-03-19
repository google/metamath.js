include "cuhgr.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "ciedg.mm"
include "cfv.mm"
include "wsbc.mm"
include "cvtx.mm"
include "cab.mm"
include "df-uhgr.mm"
include "eleq2i.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "eqcomi.mm"
include "dmeqi.mm"
include "syl6eq.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "feq123d.mm"
include "weq.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "sbcied2.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "syl5bb.mm"

theorem isuhgr
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let ve: setvar e
  assume isuhgr.v: |- V = ( Vtx ` G )
  assume isuhgr.e: |- E = ( iEdg ` G )


  assert |- ( G e. U -> ( G e. UHGraph <-> E : dom E --> ( ~P V \ { (/) } ) ) )

  proof
    cG
    cuhgr
    wcel
    cG
    ve
    cv
    #
    cdm
    #
    vv
    cv
    #
    cpw
    #
    c0
    csn
    #
    cdif
    #
    @0
    wf
    #
    ve
    vg
    cv
    #
    ciedg
    cfv
    #
    wsbc
    #
    vv
    @7
    cvtx
    cfv
    #
    wsbc
    #
    vg
    cab
    #
    wcel
    cG
    cU
    wcel
    cE
    cdm
    #
    cV
    cpw
    #
    @4
    cdif
    #
    cE
    wf
    #
    cuhgr
    @12
    cG
    vv
    ve
    vg
    df-uhgr
    eleq2i
    vh
    cv
    #
    ciedg
    cfv
    #
    cdm
    #
    @17
    cvtx
    cfv
    #
    cpw
    #
    @4
    cdif
    #
    @18
    wf
    #
    @16
    vh
    cG
    @12
    cU
    @17
    cG
    wceq
    #
    @19
    @13
    @22
    @15
    @18
    cE
    @24
    @18
    cG
    ciedg
    cfv
    #
    cE
    @17
    cG
    ciedg
    fveq2
    #
    isuhgr.e
    syl6eqr
    @24
    @19
    @25
    cdm
    @13
    @24
    @18
    @25
    @26
    dmeqd
    @25
    cE
    cE
    @25
    isuhgr.e
    eqcomi
    dmeqi
    syl6eq
    @24
    @21
    @14
    @4
    @24
    @20
    cV
    @24
    @20
    cG
    cvtx
    cfv
    cV
    @17
    cG
    cvtx
    fveq2
    isuhgr.v
    syl6eqr
    pweqd
    difeq1d
    feq123d
    @11
    @23
    vg
    vh
    vg
    vh
    weq
    #
    @9
    @23
    vv
    @10
    @20
    cvv
    @27
    @7
    cvtx
    fvexd
    @7
    @17
    cvtx
    fveq2
    @27
    @2
    @20
    wceq
    #
    wa
    #
    @6
    @23
    ve
    @8
    @18
    cvv
    @29
    @7
    ciedg
    fvexd
    @27
    @8
    @18
    wceq
    @28
    @7
    @17
    ciedg
    fveq2
    adantr
    @29
    @0
    @18
    wceq
    #
    wa
    #
    @1
    @19
    @5
    @22
    @0
    @18
    @29
    @30
    simpr
    #
    @31
    @0
    @18
    @32
    dmeqd
    @29
    @5
    @22
    wceq
    @30
    @29
    @3
    @21
    @4
    @29
    @2
    @20
    @27
    @28
    simpr
    pweqd
    difeq1d
    adantr
    feq123d
    sbcied2
    sbcied2
    cbvabv
    elab2g
    syl5bb
end
