include "wcel.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpst.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "mthmval.mm"
include "eleq2i.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "eqid.mm"
include "msrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "elpreima.mm"
include "wss.mm"
include "mppspst.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "anbi2i.mm"
include "sseli.mm"
include "msrrcl.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem elmthm
  let vx: setvar x
  let cR: class R
  let cT: class T
  let cU: class U
  let cJ: class J
  let cX: class X
  let vt: setvar t
  let cY: class Y
  assume mthmval.r: |- R = ( mStRed ` T )
  assume mthmval.j: |- J = ( mPPSt ` T )
  assume mthmval.u: |- U = ( mThm ` T )

  disjoint J x
  disjoint R x
  disjoint T x
  disjoint X x
  disjoint t x
  disjoint J t
  disjoint R t
  disjoint T t
  disjoint Y x
  assert |- ( X e. U <-> E. x e. J ( R ` x ) = ( R ` X ) )

  proof
    cX
    cU
    wcel
    cX
    cR
    ccnv
    cR
    cJ
    cima
    #
    cima
    #
    wcel
    #
    cX
    cT
    cmpst
    cfv
    #
    wcel
    #
    cX
    cR
    cfv
    #
    @0
    wcel
    #
    wa
    #
    vx
    cv
    #
    cR
    cfv
    @5
    wceq
    #
    vx
    cJ
    wrex
    #
    cU
    @1
    cX
    cR
    cT
    cU
    cJ
    mthmval.r
    mthmval.j
    mthmval.u
    mthmval
    eleq2i
    cR
    @3
    wfn
    #
    @2
    @7
    wb
    @3
    @3
    cR
    wf
    @11
    @3
    cR
    cT
    @3
    eqid
    #
    mthmval.r
    msrf
    @3
    @3
    cR
    ffn
    ax-mp
    #
    @3
    cX
    @0
    cR
    elpreima
    ax-mp
    @7
    @4
    @10
    wa
    @10
    @6
    @10
    @4
    @11
    cJ
    @3
    wss
    @6
    @10
    wb
    @13
    @3
    cT
    cJ
    @12
    mthmval.j
    mppspst
    #
    vx
    @3
    cJ
    @5
    cR
    fvelimab
    mp2an
    anbi2i
    @10
    @4
    @9
    @4
    vx
    cJ
    @8
    cJ
    wcel
    @8
    @3
    wcel
    @9
    @4
    cJ
    @3
    @8
    @14
    sseli
    @3
    cR
    cT
    @8
    cX
    @12
    mthmval.r
    msrrcl
    syl5ibcom
    rexlimiv
    pm4.71ri
    bitr4i
    3bitri
end
