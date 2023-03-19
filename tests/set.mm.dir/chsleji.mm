include "chshii.mm"
include "shsleji.mm"

theorem chsleji
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A +H B ) C_ ( A vH B )

  proof
    cA
    cB
    cA
    ch0le.1
    chshii
    cB
    chjcl.2
    chshii
    shsleji
end
