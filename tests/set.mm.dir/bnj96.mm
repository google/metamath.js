include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "c-bnj14.mm"
include "cop.mm"
include "csn.mm"
include "cdm.mm"
include "c1o.mm"
include "cvv.mm"
include "wceq.mm"
include "bnj93.mm"
include "dmsnopg.mm"
include "syl.mm"
include "dmeqi.mm"
include "df1o2.mm"
include "3eqtr4g.mm"

theorem bnj96
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  assume bnj96.1: |- F = { <. (/) , _pred ( x , A , R ) >. }

  disjoint A x
  disjoint R x
  assert |- ( ( R _FrSe A /\ x e. A ) -> dom F = 1o )

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
    c0
    cA
    cR
    @0
    c-bnj14
    #
    cop
    csn
    #
    cdm
    #
    c0
    csn
    #
    cF
    cdm
    c1o
    @1
    @2
    cvv
    wcel
    @4
    @5
    wceq
    vx
    cA
    cR
    bnj93
    c0
    @2
    cvv
    dmsnopg
    syl
    cF
    @3
    bnj96.1
    dmeqi
    df1o2
    3eqtr4g
end
