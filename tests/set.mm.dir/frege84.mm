include "wcel.mm"
include "whe.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "frege81.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege84
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


  assert |- ( R hereditary A -> ( X e. A -> ( X ( t+ ` R ) Y -> Y e. A ) ) )

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
    cY
    cR
    ctcl
    cfv
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
    cB
    cR
    cU
    cV
    cW
    cX
    cY
    frege84.x
    frege84.y
    frege84.r
    frege84.a
    frege81
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
