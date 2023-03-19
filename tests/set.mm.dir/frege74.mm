include "whe.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "frege72.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege74
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  assume frege74.x: |- X e. U
  assume frege74.y: |- Y e. V


  assert |- ( X e. A -> ( R hereditary A -> ( X R Y -> Y e. A ) ) )

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
    @1
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
    frege74.x
    frege74.y
    frege72
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
