include "chshii.mm"
include "shjcli.mm"

theorem chjcli
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A vH B ) e. CH

  proof
    cA
    cB
    cA
    ch0le.1
    chshii
    cB
    chjcl.2
    chshii
    shjcli
end
