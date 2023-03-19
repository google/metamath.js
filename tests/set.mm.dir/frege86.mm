include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "frege85.mm"
include "frege19.mm"
include "ax-mp.mm"

theorem frege86
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume frege86.x: |- X e. U
  assume frege86.y: |- Y e. V
  assume frege86.r: |- R e. W
  assume frege86.a: |- A e. B

  disjoint A w
  disjoint R w
  disjoint X w
  assert |- ( ( ( R hereditary A -> Y e. A ) -> ( R hereditary A -> ( Y R Z -> Z e. A ) ) ) -> ( X ( t+ ` R ) Y -> ( A. w ( X R w -> w e. A ) -> ( R hereditary A -> ( Y R Z -> Z e. A ) ) ) ) )

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
    cA
    wcel
    wi
    #
    wi
    wi
    @4
    @3
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
    @0
    @2
    @5
    wi
    wi
    wi
    vw
    cA
    cB
    cR
    cU
    cV
    cW
    cX
    cY
    frege86.x
    frege86.y
    frege86.r
    frege86.a
    frege85
    @0
    @2
    @4
    @5
    frege19
    ax-mp
end
