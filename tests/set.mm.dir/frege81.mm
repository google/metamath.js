include "wcel.mm"
include "whe.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "ctcl.mm"
include "cfv.mm"
include "cvv.mm"
include "vex.mm"
include "frege74.mm"
include "alrimdv.mm"
include "frege80.mm"
include "ax-mp.mm"

theorem frege81
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege81.x: |- X e. U
  assume frege81.y: |- Y e. V
  assume frege81.r: |- R e. W
  assume frege81.a: |- A e. B


  assert |- ( X e. A -> ( R hereditary A -> ( X ( t+ ` R ) Y -> Y e. A ) ) )

  proof
    cX
    cA
    wcel
    #
    cA
    cR
    whe
    #
    cX
    va
    cv
    #
    cR
    wbr
    @2
    cA
    wcel
    wi
    #
    va
    wal
    wi
    wi
    @0
    @1
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    cY
    cA
    wcel
    wi
    wi
    wi
    @0
    @1
    @3
    va
    cA
    cR
    cU
    cvv
    cX
    @2
    frege81.x
    va
    vex
    frege74
    alrimdv
    cA
    cB
    cR
    cU
    cV
    cW
    cX
    cY
    va
    frege81.x
    frege81.y
    frege81.r
    frege81.a
    frege80
    ax-mp
end
