include "ciin.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "elin.mm"
include "eliin.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem elriin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cX: class X
  let vy: setvar y

  disjoint A x
  disjoint X x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint X y
  assert |- ( B e. ( A i^i |^|_ x e. X S ) <-> ( B e. A /\ A. x e. X B e. S ) )

  proof
    cB
    cA
    vx
    cX
    cS
    ciin
    #
    cin
    wcel
    cB
    cA
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    @1
    cB
    cS
    wcel
    vx
    cX
    wral
    #
    wa
    cB
    cA
    @0
    elin
    @1
    @2
    @3
    vx
    cB
    cX
    cS
    cA
    eliin
    pm5.32i
    bitri
end
