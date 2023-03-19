include "cwdom.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "brwdom.mm"
include "syl.mm"
include "ibi.mm"

theorem brwdomi
  let vz: setvar z
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cF: class F
  let cZ: class Z

  disjoint X z
  disjoint Y z
  disjoint X x
  disjoint X y
  disjoint X w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint Y x
  disjoint Y y
  disjoint Y w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint Z w
  assert |- ( X ~<_* Y -> ( X = (/) \/ E. z z : Y -onto-> X ) )

  proof
    cX
    cY
    cwdom
    wbr
    #
    cX
    c0
    wceq
    cY
    cX
    vz
    cv
    wfo
    vz
    wex
    wo
    #
    @0
    cY
    cvv
    wcel
    @0
    @1
    wb
    cX
    cY
    cwdom
    relwdom
    brrelex2i
    vz
    cvv
    cX
    cY
    brwdom
    syl
    ibi
end
