include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "whe.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "frege77.mm"
include "frege17.mm"
include "ax-mp.mm"

theorem frege78
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege78.x: |- X e. U
  assume frege78.y: |- Y e. V
  assume frege78.r: |- R e. W
  assume frege78.a: |- A e. B

  disjoint A a
  disjoint R a
  disjoint X a
  assert |- ( R hereditary A -> ( A. a ( X R a -> a e. A ) -> ( X ( t+ ` R ) Y -> Y e. A ) ) )

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
    va
    cv
    #
    cR
    wbr
    @2
    cA
    wcel
    wi
    va
    wal
    #
    cY
    cA
    wcel
    #
    wi
    wi
    wi
    @1
    @3
    @0
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
    va
    frege78.x
    frege78.y
    frege78.r
    frege78.a
    frege77
    @0
    @1
    @3
    @4
    frege17
    ax-mp
end
