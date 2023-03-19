include "chshii.mm"
include "shseli.mm"

theorem chseli
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( C e. ( A +H B ) <-> E. x e. A E. y e. B C = ( x +h y ) )

  proof
    vx
    vy
    cA
    cB
    cC
    cA
    ch0le.1
    chshii
    cB
    chjcl.2
    chshii
    shseli
end
