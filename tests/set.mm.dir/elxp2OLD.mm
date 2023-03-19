include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "cxp.mm"
include "df-rex.mm"
include "r19.42v.mm"
include "an13.mm"
include "exbii.mm"
include "3bitr3i.mm"
include "elxp.mm"
include "3bitr4ri.mm"

theorem elxp2OLD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  assert |- ( A e. ( B X. C ) <-> E. x e. B E. y e. C A = <. x , y >. )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    cA
    @0
    vy
    cv
    #
    cop
    wceq
    #
    vy
    cC
    wrex
    #
    wa
    #
    vx
    wex
    @3
    @1
    @2
    cC
    wcel
    #
    wa
    wa
    #
    vy
    wex
    #
    vx
    wex
    @4
    vx
    cB
    wrex
    cA
    cB
    cC
    cxp
    wcel
    @5
    @8
    vx
    @1
    @3
    wa
    #
    vy
    cC
    wrex
    @6
    @9
    wa
    #
    vy
    wex
    @5
    @8
    @9
    vy
    cC
    df-rex
    @1
    @3
    vy
    cC
    r19.42v
    @10
    @7
    vy
    @6
    @1
    @3
    an13
    exbii
    3bitr3i
    exbii
    @4
    vx
    cB
    df-rex
    vx
    vy
    cA
    cB
    cC
    elxp
    3bitr4ri
end
