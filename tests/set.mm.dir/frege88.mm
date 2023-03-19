include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "frege87.mm"
include "frege15.mm"
include "ax-mp.mm"

theorem frege88
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume frege87.x: |- X e. U
  assume frege87.y: |- Y e. V
  assume frege87.z: |- Z e. W
  assume frege87.r: |- R e. S
  assume frege87.a: |- A e. B

  disjoint A w
  disjoint R w
  disjoint X w
  assert |- ( Y R Z -> ( X ( t+ ` R ) Y -> ( A. w ( X R w -> w e. A ) -> ( R hereditary A -> Z e. A ) ) ) )

  proof
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    #
    cX
    vw
    cv
    #
    cR
    wbr
    @1
    cA
    wcel
    wi
    vw
    wal
    #
    cA
    cR
    whe
    #
    cY
    cZ
    cR
    wbr
    #
    cZ
    cA
    wcel
    #
    wi
    wi
    wi
    wi
    @4
    @0
    @2
    @3
    @5
    wi
    wi
    wi
    wi
    vw
    cA
    cB
    cR
    cS
    cU
    cV
    cW
    cX
    cY
    cZ
    frege87.x
    frege87.y
    frege87.z
    frege87.r
    frege87.a
    frege87
    @0
    @2
    @3
    @4
    @5
    frege15
    ax-mp
end
