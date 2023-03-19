include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "df-ne.mm"
include "neq0f.mm"
include "bitri.mm"

theorem n0f
  let vx: setvar x
  let cA: class A
  assume eq0f.1: |- F/_ x A


  assert |- ( A =/= (/) <-> E. x x e. A )

  proof
    cA
    c0
    wne
    cA
    c0
    wceq
    wn
    vx
    cv
    cA
    wcel
    vx
    wex
    cA
    c0
    df-ne
    vx
    cA
    eq0f.1
    neq0f
    bitri
end
