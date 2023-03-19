include "cmthm.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmsr.mm"
include "cmpps.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "imaeq12d.mm"
include "df-mthm.mm"
include "fvex.mm"
include "cnvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "fvmpt3i.mm"
include "wn.mm"
include "c0.mm"
include "0ima.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "cnv0.mm"
include "syl6eq.mm"
include "imaeq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mthmval
  let cR: class R
  let cT: class T
  let cU: class U
  let cJ: class J
  let vt: setvar t
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume mthmval.r: |- R = ( mStRed ` T )
  assume mthmval.j: |- J = ( mPPSt ` T )
  assume mthmval.u: |- U = ( mThm ` T )


  assert |- U = ( `' R " ( R " J ) )

  proof
    cU
    cT
    cmthm
    cfv
    #
    cR
    ccnv
    #
    cR
    cJ
    cima
    #
    cima
    #
    mthmval.u
    cT
    cvv
    wcel
    #
    @0
    @3
    wceq
    vt
    cT
    vt
    cv
    #
    cmsr
    cfv
    #
    ccnv
    #
    @6
    @5
    cmpps
    cfv
    #
    cima
    #
    cima
    #
    @3
    cvv
    cmthm
    @5
    cT
    wceq
    #
    @7
    @1
    @9
    @2
    @11
    @6
    cR
    @11
    @6
    cT
    cmsr
    cfv
    #
    cR
    @5
    cT
    cmsr
    fveq2
    mthmval.r
    syl6eqr
    #
    cnveqd
    @11
    @6
    cR
    @8
    cJ
    @13
    @11
    @8
    cT
    cmpps
    cfv
    cJ
    @5
    cT
    cmpps
    fveq2
    mthmval.j
    syl6eqr
    imaeq12d
    imaeq12d
    vt
    df-mthm
    @7
    cvv
    wcel
    @10
    cvv
    wcel
    @6
    @5
    cmsr
    fvex
    cnvex
    @7
    @9
    cvv
    imaexg
    ax-mp
    fvmpt3i
    @4
    wn
    #
    c0
    c0
    @2
    cima
    #
    @0
    @3
    @15
    c0
    @2
    0ima
    eqcomi
    cT
    cmthm
    fvprc
    @14
    @1
    c0
    @2
    @14
    @1
    c0
    ccnv
    c0
    @14
    cR
    c0
    @14
    cR
    @12
    c0
    mthmval.r
    cT
    cmsr
    fvprc
    syl5eq
    cnveqd
    cnv0
    syl6eq
    imaeq1d
    3eqtr4a
    pm2.61i
    eqtri
end
