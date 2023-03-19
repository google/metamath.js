include "wcel.mm"
include "c0.mm"
include "cwdom.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "eqid.mm"
include "orci.mm"
include "brwdom.mm"
include "mpbiri.mm"

theorem 0wdom
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cY: class Y
  let cF: class F
  let cZ: class Z


  assert |- ( X e. V -> (/) ~<_* X )

  proof
    cX
    cV
    wcel
    c0
    cX
    cwdom
    wbr
    c0
    c0
    wceq
    #
    cX
    c0
    vz
    cv
    wfo
    vz
    wex
    #
    wo
    @0
    @1
    c0
    eqid
    orci
    vz
    cV
    c0
    cX
    brwdom
    mpbiri
end
