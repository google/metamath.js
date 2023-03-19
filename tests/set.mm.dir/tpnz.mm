include "ctp.mm"
include "tpid1.mm"
include "ne0ii.mm"

theorem tpnz
  let cA: class A
  let cB: class B
  let cC: class C
  assume tpnz.1: |- A e. _V


  assert |- { A , B , C } =/= (/)

  proof
    cA
    cA
    cB
    cC
    ctp
    cA
    cB
    cC
    tpnz.1
    tpid1
    ne0ii
end
