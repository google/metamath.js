include "ccnv.mm"
include "wfun.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "frege118.mm"
include "frege19.mm"
include "ax-mp.mm"

theorem frege119
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege116.x: |- X e. U
  assume frege118.y: |- Y e. V

  disjoint R a
  disjoint X a
  disjoint Y a
  assert |- ( ( A. a ( Y R a -> a = X ) -> ( Y R A -> A = X ) ) -> ( Fun `' `' R -> ( Y R X -> ( Y R A -> A = X ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    cY
    cX
    cR
    wbr
    #
    cY
    va
    cv
    #
    cR
    wbr
    @2
    cX
    wceq
    wi
    va
    wal
    #
    wi
    wi
    @3
    cY
    cA
    cR
    wbr
    cA
    cX
    wceq
    wi
    #
    wi
    @0
    @1
    @4
    wi
    wi
    wi
    cR
    cU
    cV
    cX
    cY
    va
    frege116.x
    frege118.y
    frege118
    @0
    @1
    @3
    @4
    frege19
    ax-mp
end
