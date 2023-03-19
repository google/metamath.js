include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "nnsuc.mm"
include "sylan2br.mm"
include "ex.mm"
include "orrd.mm"

theorem nn0suc
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. _om -> ( A = (/) \/ E. x e. _om A = suc x ) )

  proof
    cA
    com
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    vx
    cv
    csuc
    wceq
    vx
    com
    wrex
    #
    @0
    @1
    wn
    #
    @2
    @3
    @0
    cA
    c0
    wne
    @2
    cA
    c0
    df-ne
    vx
    cA
    nnsuc
    sylan2br
    ex
    orrd
end
