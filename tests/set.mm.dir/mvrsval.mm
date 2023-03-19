include "wcel.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "crn.mm"
include "cin.mm"
include "cvv.mm"
include "cmvrs.mm"
include "cmpt.mm"
include "wceq.mm"
include "cmex.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "cmvar.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "ineq2d.mm"
include "mpteq12dv.mm"
include "df-mvrs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "ineq1d.mm"
include "adantl.mm"
include "id.mm"
include "rnex.mm"
include "inex1.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem mvrsval
  let cT: class T
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let ve: setvar e
  let vt: setvar t
  assume mvrsval.v: |- V = ( mVR ` T )
  assume mvrsval.e: |- E = ( mEx ` T )
  assume mvrsval.w: |- W = ( mVars ` T )


  assert |- ( X e. E -> ( W ` X ) = ( ran ( 2nd ` X ) i^i V ) )

  proof
    cX
    cE
    wcel
    #
    ve
    cX
    ve
    cv
    #
    c2nd
    cfv
    #
    crn
    #
    cV
    cin
    #
    cX
    c2nd
    cfv
    #
    crn
    #
    cV
    cin
    #
    cE
    cW
    cvv
    @0
    cW
    cT
    cmvrs
    cfv
    #
    ve
    cE
    @4
    cmpt
    #
    mvrsval.w
    @0
    cT
    cvv
    wcel
    #
    @8
    @9
    wceq
    @10
    cX
    cT
    cmex
    cfv
    #
    cE
    cX
    cT
    cmex
    elfvex
    mvrsval.e
    eleq2s
    vt
    cT
    ve
    vt
    cv
    #
    cmex
    cfv
    #
    @3
    @12
    cmvar
    cfv
    #
    cin
    #
    cmpt
    @9
    cvv
    cmvrs
    @12
    cT
    wceq
    #
    ve
    @13
    @15
    cE
    @4
    @16
    @13
    @11
    cE
    @12
    cT
    cmex
    fveq2
    mvrsval.e
    syl6eqr
    @16
    @14
    cV
    @3
    @16
    @14
    cT
    cmvar
    cfv
    cV
    @12
    cT
    cmvar
    fveq2
    mvrsval.v
    syl6eqr
    ineq2d
    mpteq12dv
    vt
    ve
    df-mvrs
    ve
    cE
    @4
    cE
    @11
    cvv
    mvrsval.e
    cT
    cmex
    fvex
    eqeltri
    mptex
    fvmpt
    syl
    syl5eq
    @1
    cX
    wceq
    #
    @4
    @7
    wceq
    @0
    @17
    @3
    @6
    cV
    @17
    @2
    @5
    @1
    cX
    c2nd
    fveq2
    rneqd
    ineq1d
    adantl
    @0
    id
    @7
    cvv
    wcel
    @0
    @6
    cV
    @5
    cX
    c2nd
    fvex
    rnex
    inex1
    a1i
    fvmptd
end
