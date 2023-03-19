include "wss.mm"
include "chj.mm"
include "co.mm"
include "chlej1i.mm"
include "chlej2i.mm"
include "sylan9ss.mm"

theorem chlej12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH
  assume chlub.1: |- C e. CH
  assume chlej12.4: |- D e. CH


  assert |- ( ( A C_ B /\ C C_ D ) -> ( A vH C ) C_ ( B vH D ) )

  proof
    cA
    cB
    wss
    cC
    cD
    wss
    cA
    cC
    chj
    co
    cB
    cC
    chj
    co
    cB
    cD
    chj
    co
    cA
    cB
    cC
    ch0le.1
    chjcl.2
    chlub.1
    chlej1i
    cC
    cD
    cB
    chlub.1
    chlej12.4
    chjcl.2
    chlej2i
    sylan9ss
end
