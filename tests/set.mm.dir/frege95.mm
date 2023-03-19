include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "cv.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wcel.mm"
include "cvv.mm"
include "vex.mm"
include "frege88.mm"
include "alrimdv.mm"
include "frege94.mm"
include "ax-mp.mm"

theorem frege95
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vw: setvar w
  assume frege95.x: |- X e. U
  assume frege95.y: |- Y e. V
  assume frege95.z: |- Z e. W
  assume frege95.r: |- R e. A


  assert |- ( Y R Z -> ( X ( t+ ` R ) Y -> X ( t+ ` R ) Z ) )

  proof
    cY
    cZ
    cR
    wbr
    #
    cX
    cY
    cR
    ctcl
    cfv
    #
    wbr
    #
    cX
    vw
    cv
    cR
    wbr
    vw
    vf
    wel
    wi
    vw
    wal
    vf
    cv
    #
    cR
    whe
    cZ
    @3
    wcel
    wi
    wi
    #
    vf
    wal
    wi
    wi
    @0
    @2
    cX
    cZ
    @1
    wbr
    wi
    wi
    @0
    @2
    @4
    vf
    vw
    @3
    cvv
    cR
    cA
    cU
    cV
    cW
    cX
    cY
    cZ
    frege95.x
    frege95.y
    frege95.z
    frege95.r
    vf
    vex
    frege88
    alrimdv
    vw
    cR
    cU
    vf
    cW
    cA
    cX
    cY
    cZ
    frege95.x
    frege95.z
    frege95.r
    frege94
    ax-mp
end
