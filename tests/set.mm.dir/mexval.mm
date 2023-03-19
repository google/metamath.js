include "cmex.mm"
include "cfv.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmtc.mm"
include "cmrex.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "xpeq12d.mm"
include "df-mex.mm"
include "fvex.mm"
include "xpex.mm"
include "fvmpt3i.mm"
include "wn.mm"
include "c0.mm"
include "xp0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "xpeq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mexval
  let cR: class R
  let cT: class T
  let cE: class E
  let cK: class K
  let vt: setvar t
  assume mexval.k: |- K = ( mTC ` T )
  assume mexval.e: |- E = ( mEx ` T )
  assume mexval.r: |- R = ( mREx ` T )


  assert |- E = ( K X. R )

  proof
    cE
    cT
    cmex
    cfv
    #
    cK
    cR
    cxp
    #
    mexval.e
    cT
    cvv
    wcel
    #
    @0
    @1
    wceq
    vt
    cT
    vt
    cv
    #
    cmtc
    cfv
    #
    @3
    cmrex
    cfv
    #
    cxp
    @1
    cvv
    cmex
    @3
    cT
    wceq
    #
    @4
    cK
    @5
    cR
    @6
    @4
    cT
    cmtc
    cfv
    cK
    @3
    cT
    cmtc
    fveq2
    mexval.k
    syl6eqr
    @6
    @5
    cT
    cmrex
    cfv
    #
    cR
    @3
    cT
    cmrex
    fveq2
    mexval.r
    syl6eqr
    xpeq12d
    vt
    df-mex
    @4
    @5
    @3
    cmtc
    fvex
    @3
    cmrex
    fvex
    xpex
    fvmpt3i
    @2
    wn
    #
    c0
    cK
    c0
    cxp
    #
    @0
    @1
    @9
    c0
    cK
    xp0
    eqcomi
    cT
    cmex
    fvprc
    @8
    cR
    c0
    cK
    @8
    cR
    @7
    c0
    mexval.r
    cT
    cmrex
    fvprc
    syl5eq
    xpeq2d
    3eqtr4a
    pm2.61i
    eqtri
end
