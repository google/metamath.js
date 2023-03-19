include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul01.mm"
include "ax-mp.mm"

theorem mul01i
  let cA: class A
  assume mul.1: |- A e. CC


  assert |- ( A x. 0 ) = 0

  proof
    cA
    cc
    wcel
    cA
    cc0
    cmul
    co
    cc0
    wceq
    mul.1
    cA
    mul01
    ax-mp
end
