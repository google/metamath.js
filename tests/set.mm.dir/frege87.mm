include "whe.mm"
include "wcel.mm"
include "wi.mm"
include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "cv.mm"
include "wal.mm"
include "frege73.mm"
include "frege86.mm"
include "ax-mp.mm"

theorem frege87
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
  assert |- ( X ( t+ ` R ) Y -> ( A. w ( X R w -> w e. A ) -> ( R hereditary A -> ( Y R Z -> Z e. A ) ) ) )

  proof
    cA
    cR
    whe
    #
    cY
    cA
    wcel
    wi
    @0
    cY
    cZ
    cR
    wbr
    cZ
    cA
    wcel
    wi
    wi
    #
    wi
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    cX
    vw
    cv
    #
    cR
    wbr
    @2
    cA
    wcel
    wi
    vw
    wal
    @1
    wi
    wi
    cA
    cR
    cV
    cW
    cY
    cZ
    frege87.y
    frege87.z
    frege73
    vw
    cA
    cB
    cR
    cU
    cV
    cS
    cX
    cY
    cZ
    frege87.x
    frege87.y
    frege87.r
    frege87.a
    frege86
    ax-mp
end
