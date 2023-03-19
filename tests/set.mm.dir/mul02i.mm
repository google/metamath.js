include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul02.mm"
include "ax-mp.mm"

theorem mul02i
  let cA: class A
  assume mul.1: |- A e. CC


  assert |- ( 0 x. A ) = 0

  proof
    cA
    cc
    wcel
    cc0
    cA
    cmul
    co
    cc0
    wceq
    mul.1
    cA
    mul02
    ax-mp
end
