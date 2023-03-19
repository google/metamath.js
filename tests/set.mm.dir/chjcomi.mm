include "chshii.mm"
include "shjcomi.mm"

theorem chjcomi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A vH B ) = ( B vH A )

  proof
    cA
    cB
    cA
    ch0le.1
    chshii
    cB
    chjcl.2
    chshii
    shjcomi
end
