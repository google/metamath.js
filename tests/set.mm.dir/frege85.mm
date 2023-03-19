include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "whe.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "frege77.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege85
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege84.x: |- X e. U
  assume frege84.y: |- Y e. V
  assume frege84.r: |- R e. W
  assume frege84.a: |- A e. B

  disjoint A z
  disjoint R z
  disjoint X z
  assert |- ( X ( t+ ` R ) Y -> ( A. z ( X R z -> z e. A ) -> ( R hereditary A -> Y e. A ) ) )

  proof
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    #
    cA
    cR
    whe
    #
    cX
    vz
    cv
    #
    cR
    wbr
    @2
    cA
    wcel
    wi
    vz
    wal
    #
    cY
    cA
    wcel
    #
    wi
    wi
    wi
    @0
    @3
    @1
    @4
    wi
    wi
    wi
    cA
    cB
    cR
    cU
    cV
    cW
    cX
    cY
    vz
    frege84.x
    frege84.y
    frege84.r
    frege84.a
    frege77
    @0
    @1
    @3
    @4
    frege12
    ax-mp
end
