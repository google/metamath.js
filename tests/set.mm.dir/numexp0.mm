include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "nn0cni.mm"
include "exp0.mm"
include "ax-mp.mm"

theorem numexp0
  let cA: class A
  assume numexp.1: |- A e. NN0


  assert |- ( A ^ 0 ) = 1

  proof
    cA
    cc
    wcel
    cA
    cc0
    cexp
    co
    c1
    wceq
    cA
    numexp.1
    nn0cni
    cA
    exp0
    ax-mp
end
