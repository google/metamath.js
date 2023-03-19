include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "exancom.mm"
include "df-rex.mm"
include "df-clel.mm"
include "3bitr4ri.mm"

theorem risset
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A e. B <-> E. x e. B x = A )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    @0
    cA
    wceq
    #
    wa
    vx
    wex
    @2
    @1
    wa
    vx
    wex
    @2
    vx
    cB
    wrex
    cA
    cB
    wcel
    @1
    @2
    vx
    exancom
    @2
    vx
    cB
    df-rex
    vx
    cA
    cB
    df-clel
    3bitr4ri
end
