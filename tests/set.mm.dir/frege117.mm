include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "frege116.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege117
  let cR: class R
  let cU: class U
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume frege116.x: |- X e. U

  disjoint a b
  disjoint R a
  disjoint R b
  disjoint X a
  disjoint X b
  assert |- ( ( A. b ( b R X -> A. a ( b R a -> a = X ) ) -> ( Y R X -> A. a ( Y R a -> a = X ) ) ) -> ( Fun `' `' R -> ( Y R X -> A. a ( Y R a -> a = X ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    vb
    cv
    #
    cX
    cR
    wbr
    @1
    va
    cv
    #
    cR
    wbr
    @2
    cX
    wceq
    #
    wi
    va
    wal
    wi
    vb
    wal
    #
    wi
    @4
    cY
    cX
    cR
    wbr
    cY
    @2
    cR
    wbr
    @3
    wi
    va
    wal
    wi
    #
    wi
    @0
    @5
    wi
    wi
    cR
    cU
    cX
    va
    vb
    frege116.x
    frege116
    @0
    @4
    @5
    frege9
    ax-mp
end
