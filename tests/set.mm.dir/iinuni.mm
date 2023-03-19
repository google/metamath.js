include "cv.mm"
include "wcel.mm"
include "cint.mm"
include "wo.mm"
include "cab.mm"
include "cun.mm"
include "wral.mm"
include "ciin.mm"
include "r19.32v.mm"
include "elun.mm"
include "ralbii.mm"
include "vex.mm"
include "elint2.mm"
include "orbi2i.mm"
include "3bitr4ri.mm"
include "abbii.mm"
include "df-un.mm"
include "df-iin.mm"
include "3eqtr4i.mm"

theorem iinuni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A u. |^| B ) = |^|_ x e. B ( A u. x )

  proof
    vy
    cv
    #
    cA
    wcel
    #
    @0
    cB
    cint
    #
    wcel
    #
    wo
    #
    vy
    cab
    @0
    cA
    vx
    cv
    #
    cun
    #
    wcel
    #
    vx
    cB
    wral
    #
    vy
    cab
    cA
    @2
    cun
    vx
    cB
    @6
    ciin
    @4
    @8
    vy
    @1
    @0
    @5
    wcel
    #
    wo
    #
    vx
    cB
    wral
    @1
    @9
    vx
    cB
    wral
    #
    wo
    @8
    @4
    @1
    @9
    vx
    cB
    r19.32v
    @7
    @10
    vx
    cB
    @0
    cA
    @5
    elun
    ralbii
    @3
    @11
    @1
    vx
    @0
    cB
    vy
    vex
    elint2
    orbi2i
    3bitr4ri
    abbii
    vy
    cA
    @2
    df-un
    vx
    vy
    cB
    @6
    df-iin
    3eqtr4i
end
