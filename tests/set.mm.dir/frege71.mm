include "whe.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "frege70.mm"
include "frege19.mm"
include "ax-mp.mm"

theorem frege71
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  let cY: class Y
  assume frege71.x: |- X e. V

  disjoint A z
  disjoint R z
  disjoint X z
  assert |- ( ( A. z ( X R z -> z e. A ) -> ( X R Y -> Y e. A ) ) -> ( R hereditary A -> ( X e. A -> ( X R Y -> Y e. A ) ) ) )

  proof
    cA
    cR
    whe
    #
    cX
    cA
    wcel
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
    wi
    wi
    @3
    cX
    cY
    cR
    wbr
    cY
    cA
    wcel
    wi
    #
    wi
    @0
    @1
    @4
    wi
    wi
    wi
    vz
    cA
    cR
    cV
    cX
    frege71.x
    frege70
    @0
    @1
    @3
    @4
    frege19
    ax-mp
end
