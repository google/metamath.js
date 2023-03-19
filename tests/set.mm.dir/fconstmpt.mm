include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "cxp.mm"
include "cmpt.mm"
include "velsn.mm"
include "anbi2i.mm"
include "opabbii.mm"
include "df-xp.mm"
include "df-mpt.mm"
include "3eqtr4i.mm"

theorem fconstmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A X. { B } ) = ( x e. A |-> B )

  proof
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    #
    cB
    csn
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @0
    @1
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    cA
    @2
    cxp
    vx
    cA
    cB
    cmpt
    @4
    @6
    vx
    vy
    @3
    @5
    @0
    vy
    cB
    velsn
    anbi2i
    opabbii
    vx
    vy
    cA
    @2
    df-xp
    vx
    vy
    cA
    cB
    df-mpt
    3eqtr4i
end
