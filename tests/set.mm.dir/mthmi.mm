include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "elmthm.mm"
include "sylibr.mm"

theorem mthmi
  let cR: class R
  let cT: class T
  let cU: class U
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vx: setvar x
  assume mthmval.r: |- R = ( mStRed ` T )
  assume mthmval.j: |- J = ( mPPSt ` T )
  assume mthmval.u: |- U = ( mThm ` T )


  assert |- ( ( X e. J /\ ( R ` X ) = ( R ` Y ) ) -> Y e. U )

  proof
    cX
    cJ
    wcel
    cX
    cR
    cfv
    #
    cY
    cR
    cfv
    #
    wceq
    #
    wa
    vx
    cv
    #
    cR
    cfv
    #
    @1
    wceq
    #
    vx
    cJ
    wrex
    cY
    cU
    wcel
    @5
    @2
    vx
    cX
    cJ
    @3
    cX
    wceq
    @4
    @0
    @1
    @3
    cX
    cR
    fveq2
    eqeq1d
    rspcev
    vx
    cR
    cT
    cU
    cJ
    cY
    mthmval.r
    mthmval.j
    mthmval.u
    elmthm
    sylibr
end
