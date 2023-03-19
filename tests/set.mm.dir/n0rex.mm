include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "id.mm"
include "ancli.mm"
include "eximi.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4i.mm"

theorem n0rex
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) -> E. x e. A x e. A )

  proof
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    @0
    @0
    wa
    #
    vx
    wex
    cA
    c0
    wne
    @0
    vx
    cA
    wrex
    @0
    @1
    vx
    @0
    @0
    @0
    id
    ancli
    eximi
    vx
    cA
    n0
    @0
    vx
    cA
    df-rex
    3imtr4i
end
