include "cv.mm"
include "cfv.mm"
include "cs1.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "s1eq.mm"
include "opeq12d.mm"
include "mvhfval.mm"
include "opex.mm"
include "fvmpt.mm"

theorem mvhval
  let cT: class T
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vv: setvar v
  assume mvhfval.v: |- V = ( mVR ` T )
  assume mvhfval.y: |- Y = ( mType ` T )
  assume mvhfval.h: |- H = ( mVH ` T )


  assert |- ( X e. V -> ( H ` X ) = <. ( Y ` X ) , <" X "> >. )

  proof
    vv
    cX
    vv
    cv
    #
    cY
    cfv
    #
    @0
    cs1
    #
    cop
    cX
    cY
    cfv
    #
    cX
    cs1
    #
    cop
    cV
    cH
    @0
    cX
    wceq
    @1
    @3
    @2
    @4
    @0
    cX
    cY
    fveq2
    @0
    cX
    s1eq
    opeq12d
    vv
    cT
    cH
    cV
    cY
    mvhfval.v
    mvhfval.y
    mvhfval.h
    mvhfval
    @3
    @4
    opex
    fvmpt
end
