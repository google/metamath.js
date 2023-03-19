include "w-bnj15.mm"
include "cv.mm"
include "c-bnj14.mm"
include "cvv.mm"
include "wcel.mm"
include "w-bnj13.mm"
include "wral.mm"
include "wfr.mm"
include "df-bnj15.mm"
include "simprbi.mm"
include "df-bnj13.mm"
include "sylib.mm"
include "r19.21bi.mm"

theorem bnj93
  let vx: setvar x
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint R x
  assert |- ( ( R _FrSe A /\ x e. A ) -> _pred ( x , A , R ) e. _V )

  proof
    cA
    cR
    w-bnj15
    #
    cA
    cR
    vx
    cv
    c-bnj14
    cvv
    wcel
    #
    vx
    cA
    @0
    cA
    cR
    w-bnj13
    #
    @1
    vx
    cA
    wral
    @0
    cA
    cR
    wfr
    @2
    cA
    cR
    df-bnj15
    simprbi
    vx
    cA
    cR
    df-bnj13
    sylib
    r19.21bi
end
