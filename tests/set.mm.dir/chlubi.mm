include "chshii.mm"
include "shlubi.mm"

theorem chlubi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH
  assume chlub.1: |- C e. CH


  assert |- ( ( A C_ C /\ B C_ C ) <-> ( A vH B ) C_ C )

  proof
    cA
    cB
    cC
    cA
    ch0le.1
    chshii
    cB
    chjcl.2
    chshii
    chlub.1
    shlubi
end
