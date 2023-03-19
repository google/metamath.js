include "wss.mm"
include "wa.mm"
include "cun.mm"
include "pm3.2i.mm"
include "unss.mm"
include "mpbi.mm"

theorem unssi
  let cA: class A
  let cB: class B
  let cC: class C
  assume unssi.1: |- A C_ C
  assume unssi.2: |- B C_ C


  assert |- ( A u. B ) C_ C

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    cA
    cB
    cun
    cC
    wss
    @0
    @1
    unssi.1
    unssi.2
    pm3.2i
    cA
    cB
    cC
    unss
    mpbi
end
