include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "cfin1a.mm"
include "wceq.mm"
include "pweq.mm"
include "difeq1.mm"
include "eleq1d.mm"
include "orbi2d.mm"
include "raleqbidv.mm"
include "df-fin1a.mm"
include "elab2g.mm"

theorem isfin1a
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vx: setvar x
  let cB: class B
  let cX: class X

  disjoint A y
  disjoint x y
  disjoint A x
  disjoint B y
  disjoint X x
  assert |- ( A e. V -> ( A e. Fin1a <-> A. y e. ~P A ( y e. Fin \/ ( A \ y ) e. Fin ) ) )

  proof
    vy
    cv
    #
    cfn
    wcel
    #
    vx
    cv
    #
    @0
    cdif
    #
    cfn
    wcel
    #
    wo
    #
    vy
    @2
    cpw
    #
    wral
    @1
    cA
    @0
    cdif
    #
    cfn
    wcel
    #
    wo
    #
    vy
    cA
    cpw
    #
    wral
    vx
    cA
    cfin1a
    cV
    @2
    cA
    wceq
    #
    @5
    @9
    vy
    @6
    @10
    @2
    cA
    pweq
    @11
    @4
    @8
    @1
    @11
    @3
    @7
    cfn
    @2
    cA
    @0
    difeq1
    eleq1d
    orbi2d
    raleqbidv
    vx
    vy
    df-fin1a
    elab2g
end
