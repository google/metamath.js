include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "cwdom.mm"
include "df-wdom.mm"
include "relopabi.mm"

theorem relwdom
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cY: class Y
  let cF: class F
  let cZ: class Z


  assert |- Rel ~<_*

  proof
    vx
    cv
    #
    c0
    wceq
    vy
    cv
    @0
    vz
    cv
    wfo
    vz
    wex
    wo
    vx
    vy
    cwdom
    vx
    vy
    vz
    df-wdom
    relopabi
end
