include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addid1.mm"
include "ax-mp.mm"

theorem addid1i
  let cA: class A
  assume mul.1: |- A e. CC


  assert |- ( A + 0 ) = A

  proof
    cA
    cc
    wcel
    cA
    cc0
    caddc
    co
    cA
    wceq
    mul.1
    cA
    addid1
    ax-mp
end
