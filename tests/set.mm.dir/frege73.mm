include "whe.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "frege72.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem frege73
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  assume frege73.x: |- X e. U
  assume frege73.y: |- Y e. V


  assert |- ( ( R hereditary A -> X e. A ) -> ( R hereditary A -> ( X R Y -> Y e. A ) ) )

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
    cY
    cR
    wbr
    cY
    cA
    wcel
    wi
    #
    wi
    wi
    @0
    @1
    wi
    @0
    @2
    wi
    wi
    cA
    cR
    cU
    cV
    cX
    cY
    frege73.x
    frege73.y
    frege72
    @0
    @1
    @2
    ax-frege2
    ax-mp
end
