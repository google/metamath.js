include "chshii.mm"
include "shlej2i.mm"

theorem chlej2i
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH
  assume chlub.1: |- C e. CH


  assert |- ( A C_ B -> ( C vH A ) C_ ( C vH B ) )

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
    cC
    chlub.1
    chshii
    shlej2i
end
