include "cv.mm"
include "cmcn.mm"
include "cfv.mm"
include "cmvar.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cmtc.mm"
include "cmty.mm"
include "wf.mm"
include "wa.mm"
include "cmax.mm"
include "cmsta.mm"
include "wss.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cmvt.mm"
include "wral.mm"
include "cmfs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "feq123d.mm"
include "anbi12d.mm"
include "sseq12d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "notbid.mm"
include "raleqbidv.mm"
include "df-mfs.mm"
include "elab2g.mm"

theorem ismfs
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cY: class Y
  let vt: setvar t
  assume ismfs.c: |- C = ( mCN ` T )
  assume ismfs.v: |- V = ( mVR ` T )
  assume ismfs.y: |- Y = ( mType ` T )
  assume ismfs.f: |- F = ( mVT ` T )
  assume ismfs.k: |- K = ( mTC ` T )
  assume ismfs.a: |- A = ( mAx ` T )
  assume ismfs.s: |- S = ( mStat ` T )

  disjoint F v
  disjoint T v
  disjoint A t
  disjoint C t
  disjoint t v
  disjoint F t
  disjoint K t
  disjoint S t
  disjoint T t
  disjoint V t
  disjoint Y t
  assert |- ( T e. W -> ( T e. mFS <-> ( ( ( C i^i V ) = (/) /\ Y : V --> K ) /\ ( A C_ S /\ A. v e. F -. ( `' Y " { v } ) e. Fin ) ) ) )

  proof
    vt
    cv
    #
    cmcn
    cfv
    #
    @0
    cmvar
    cfv
    #
    cin
    #
    c0
    wceq
    #
    @2
    @0
    cmtc
    cfv
    #
    @0
    cmty
    cfv
    #
    wf
    #
    wa
    #
    @0
    cmax
    cfv
    #
    @0
    cmsta
    cfv
    #
    wss
    #
    @6
    ccnv
    #
    vv
    cv
    csn
    #
    cima
    #
    cfn
    wcel
    #
    wn
    #
    vv
    @0
    cmvt
    cfv
    #
    wral
    #
    wa
    #
    wa
    cC
    cV
    cin
    #
    c0
    wceq
    #
    cV
    cK
    cY
    wf
    #
    wa
    #
    cA
    cS
    wss
    #
    cY
    ccnv
    #
    @13
    cima
    #
    cfn
    wcel
    #
    wn
    #
    vv
    cF
    wral
    #
    wa
    #
    wa
    vt
    cT
    cmfs
    cW
    @0
    cT
    wceq
    #
    @8
    @23
    @19
    @30
    @31
    @4
    @21
    @7
    @22
    @31
    @3
    @20
    c0
    @31
    @1
    cC
    @2
    cV
    @31
    @1
    cT
    cmcn
    cfv
    cC
    @0
    cT
    cmcn
    fveq2
    ismfs.c
    syl6eqr
    @31
    @2
    cT
    cmvar
    cfv
    cV
    @0
    cT
    cmvar
    fveq2
    ismfs.v
    syl6eqr
    #
    ineq12d
    eqeq1d
    @31
    @2
    cV
    @5
    cK
    @6
    cY
    @31
    @6
    cT
    cmty
    cfv
    cY
    @0
    cT
    cmty
    fveq2
    ismfs.y
    syl6eqr
    #
    @32
    @31
    @5
    cT
    cmtc
    cfv
    cK
    @0
    cT
    cmtc
    fveq2
    ismfs.k
    syl6eqr
    feq123d
    anbi12d
    @31
    @11
    @24
    @18
    @29
    @31
    @9
    cA
    @10
    cS
    @31
    @9
    cT
    cmax
    cfv
    cA
    @0
    cT
    cmax
    fveq2
    ismfs.a
    syl6eqr
    @31
    @10
    cT
    cmsta
    cfv
    cS
    @0
    cT
    cmsta
    fveq2
    ismfs.s
    syl6eqr
    sseq12d
    @31
    @16
    @28
    vv
    @17
    cF
    @31
    @17
    cT
    cmvt
    cfv
    cF
    @0
    cT
    cmvt
    fveq2
    ismfs.f
    syl6eqr
    @31
    @15
    @27
    @31
    @14
    @26
    cfn
    @31
    @12
    @25
    @13
    @31
    @6
    cY
    @33
    cnveqd
    imaeq1d
    eleq1d
    notbid
    raleqbidv
    anbi12d
    anbi12d
    vv
    vt
    df-mfs
    elab2g
end
