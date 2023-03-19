include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "cdif.mm"
include "dfin4.mm"
include "difelros.mm"
include "syld3an3.mm"
include "syl5eqel.mm"

theorem inelros
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cS: class S
  let cO: class O
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  assume isros.1: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }

  disjoint O s
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint S u
  disjoint S v
  disjoint s u
  disjoint s v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( S e. Q /\ A e. S /\ B e. S ) -> ( A i^i B ) e. S )

  proof
    cS
    cQ
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    cA
    cB
    cin
    cA
    cA
    cB
    cdif
    #
    cdif
    #
    cS
    cA
    cB
    dfin4
    @0
    @1
    @2
    @3
    cS
    wcel
    @4
    cS
    wcel
    vx
    vy
    cA
    cB
    cQ
    cS
    cO
    vs
    isros.1
    difelros
    vx
    vy
    cA
    @3
    cQ
    cS
    cO
    vs
    isros.1
    difelros
    syld3an3
    syl5eqel
end
