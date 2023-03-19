include "cv.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "vtocl2ga.mm"

theorem issubgoilem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let cY: class Y
  assume issubgoilem.1: |- ( ( x e. Y /\ y e. Y ) -> ( x H y ) = ( x G y ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint Y x
  disjoint Y y
  assert |- ( ( A e. Y /\ B e. Y ) -> ( A H B ) = ( A G B ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @0
    @1
    cG
    co
    #
    wceq
    cA
    @1
    cH
    co
    #
    cA
    @1
    cG
    co
    #
    wceq
    cA
    cB
    cH
    co
    #
    cA
    cB
    cG
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cY
    cY
    @0
    cA
    wceq
    @2
    @4
    @3
    @5
    @0
    cA
    @1
    cH
    oveq1
    @0
    cA
    @1
    cG
    oveq1
    eqeq12d
    @1
    cB
    wceq
    @4
    @6
    @5
    @7
    @1
    cB
    cA
    cH
    oveq2
    @1
    cB
    cA
    cG
    oveq2
    eqeq12d
    issubgoilem.1
    vtocl2ga
end
