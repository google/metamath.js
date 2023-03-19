include "whe.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ctcl.mm"
include "cfv.mm"
include "frege78.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem frege79
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege79.x: |- X e. U
  assume frege79.y: |- Y e. V
  assume frege79.r: |- R e. W
  assume frege79.a: |- A e. B

  disjoint A a
  disjoint R a
  disjoint X a
  assert |- ( ( R hereditary A -> A. a ( X R a -> a e. A ) ) -> ( R hereditary A -> ( X ( t+ ` R ) Y -> Y e. A ) ) )

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
    @0
    @2
    wi
    @0
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
    frege79.x
    frege79.y
    frege79.r
    frege79.a
    frege78
    @0
    @2
    @3
    ax-frege2
    ax-mp
end
