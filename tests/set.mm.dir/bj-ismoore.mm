include "cv.mm"
include "cuni.mm"
include "cint.mm"
include "cin.mm"
include "wcel.mm"
include "cpw.mm"
include "wral.mm"
include "cmoore.mm"
include "wceq.mm"
include "pweq.mm"
include "unieq.mm"
include "ineq1d.mm"
include "id.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "df-bj-moore.mm"
include "elab2g.mm"

theorem bj-ismoore
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. V -> ( A e. Moore_ <-> A. x e. ~P A ( U. A i^i |^| x ) e. A ) )

  proof
    vy
    cv
    #
    cuni
    #
    vx
    cv
    cint
    #
    cin
    #
    @0
    wcel
    #
    vx
    @0
    cpw
    #
    wral
    cA
    cuni
    #
    @2
    cin
    #
    cA
    wcel
    #
    vx
    cA
    cpw
    #
    wral
    vy
    cA
    cmoore
    cV
    @0
    cA
    wceq
    #
    @4
    @8
    vx
    @5
    @9
    @0
    cA
    pweq
    @10
    @3
    @7
    @0
    cA
    @10
    @1
    @6
    @2
    @0
    cA
    unieq
    ineq1d
    @10
    id
    eleq12d
    raleqbidv
    vy
    vx
    df-bj-moore
    elab2g
end
