include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "chlubi.mm"
include "biimpi.mm"

theorem chlubii
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH
  assume chlub.1: |- C e. CH


  assert |- ( ( A C_ C /\ B C_ C ) -> ( A vH B ) C_ C )

  proof
    cA
    cC
    wss
    cB
    cC
    wss
    wa
    cA
    cB
    chj
    co
    cC
    wss
    cA
    cB
    cC
    ch0le.1
    chjcl.2
    chlub.1
    chlubi
    biimpi
end
