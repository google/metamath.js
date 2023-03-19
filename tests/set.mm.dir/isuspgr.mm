include "cuspgr.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "ciedg.mm"
include "wsbc.mm"
include "cvtx.mm"
include "cab.mm"
include "df-uspgr.mm"
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
include "rabeqdv.mm"
include "f1eq123d.mm"
include "weq.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "pweq.mm"
include "ad2antlr.mm"
include "sbcied2.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "syl5bb.mm"

theorem isuspgr
  let vx: setvar x
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isuspgr.v: |- V = ( Vtx ` G )
  assume isuspgr.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint V x
  disjoint e g
  disjoint e h
  disjoint e v
  disjoint e x
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint h v
  disjoint h x
  disjoint v x
  disjoint E h
  disjoint G h
  disjoint V h
  assert |- ( G e. U -> ( G e. USPGraph <-> E : dom E -1-1-> { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 } ) )

  proof
    cG
    cuspgr
    wcel
    cG
    ve
    cv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vx
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
    crab
    #
    @0
    wf1
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
    @9
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
    @2
    vx
    cV
    cpw
    #
    @5
    cdif
    #
    crab
    #
    cE
    wf1
    #
    cuspgr
    @14
    cG
    vx
    vv
    ve
    vg
    df-uspgr
    eleq2i
    vh
    cv
    #
    ciedg
    cfv
    #
    cdm
    #
    @2
    vx
    @20
    cvtx
    cfv
    #
    cpw
    #
    @5
    cdif
    #
    crab
    #
    @21
    wf1
    #
    @19
    vh
    cG
    @14
    cU
    @20
    cG
    wceq
    #
    @22
    @15
    @26
    @18
    @21
    cE
    @28
    @21
    cG
    ciedg
    cfv
    #
    cE
    @20
    cG
    ciedg
    fveq2
    #
    isuspgr.e
    syl6eqr
    @28
    @22
    @29
    cdm
    @15
    @28
    @21
    @29
    @30
    dmeqd
    @29
    cE
    cE
    @29
    isuspgr.e
    eqcomi
    dmeqi
    syl6eq
    @28
    @2
    vx
    @25
    @17
    @28
    @24
    @16
    @5
    @28
    @23
    cV
    @28
    @23
    cG
    cvtx
    cfv
    cV
    @20
    cG
    cvtx
    fveq2
    isuspgr.v
    syl6eqr
    pweqd
    difeq1d
    rabeqdv
    f1eq123d
    @13
    @27
    vg
    vh
    vg
    vh
    weq
    #
    @11
    @27
    vv
    @12
    @23
    cvv
    @31
    @9
    cvtx
    fvexd
    @9
    @20
    cvtx
    fveq2
    @31
    @3
    @23
    wceq
    #
    wa
    #
    @8
    @27
    ve
    @10
    @21
    cvv
    @33
    @9
    ciedg
    fvexd
    @31
    @10
    @21
    wceq
    @32
    @9
    @20
    ciedg
    fveq2
    adantr
    @33
    @0
    @21
    wceq
    #
    wa
    #
    @1
    @22
    @7
    @26
    @0
    @21
    @33
    @34
    simpr
    #
    @35
    @0
    @21
    @36
    dmeqd
    @35
    @2
    vx
    @6
    @25
    @35
    @4
    @24
    @5
    @32
    @4
    @24
    wceq
    @31
    @34
    @3
    @23
    pweq
    ad2antlr
    difeq1d
    rabeqdv
    f1eq123d
    sbcied2
    sbcied2
    cbvabv
    elab2g
    syl5bb
end
