include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "c0.mm"
include "c-bnj14.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "bnj93.mm"
include "csn.mm"
include "0ex.mm"
include "bnj519.mm"
include "funeqi.mm"
include "sylibr.mm"
include "syl.mm"
include "opex.mm"
include "snid.mm"
include "eleqtrri.mm"
include "funopfv.mm"
include "mpisyl.mm"

theorem bnj97
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  assume bnj96.1: |- F = { <. (/) , _pred ( x , A , R ) >. }

  disjoint A x
  disjoint R x
  assert |- ( ( R _FrSe A /\ x e. A ) -> ( F ` (/) ) = _pred ( x , A , R ) )

  proof
    cA
    cR
    w-bnj15
    vx
    cv
    #
    cA
    wcel
    wa
    #
    cF
    wfun
    #
    c0
    cA
    cR
    @0
    c-bnj14
    #
    cop
    #
    cF
    wcel
    c0
    cF
    cfv
    @3
    wceq
    @1
    @3
    cvv
    wcel
    #
    @2
    vx
    cA
    cR
    bnj93
    @5
    @4
    csn
    #
    wfun
    @2
    c0
    @3
    0ex
    bnj519
    cF
    @6
    bnj96.1
    funeqi
    sylibr
    syl
    @4
    @6
    cF
    @4
    c0
    @3
    opex
    snid
    bnj96.1
    eleqtrri
    c0
    @3
    cF
    funopfv
    mpisyl
end
