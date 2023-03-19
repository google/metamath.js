include "whe.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ctcl.mm"
include "cfv.mm"
include "frege79.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege80
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege80.x: |- X e. U
  assume frege80.y: |- Y e. V
  assume frege80.r: |- R e. W
  assume frege80.a: |- A e. B

  disjoint A a
  disjoint R a
  disjoint X a
  assert |- ( ( X e. A -> ( R hereditary A -> A. a ( X R a -> a e. A ) ) ) -> ( X e. A -> ( R hereditary A -> ( X ( t+ ` R ) Y -> Y e. A ) ) ) )

  proof
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
    @1
    cA
    wcel
    wi
    va
    wal
    wi
    #
    @0
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
    #
    wi
    cX
    cA
    wcel
    #
    @2
    wi
    @4
    @3
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
    va
    frege80.x
    frege80.y
    frege80.r
    frege80.a
    frege79
    @2
    @3
    @4
    frege5
    ax-mp
end
