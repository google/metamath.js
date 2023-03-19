include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "nn0cni.mm"
include "exp1.mm"
include "ax-mp.mm"

theorem numexp1
  let cA: class A
  assume numexp.1: |- A e. NN0


  assert |- ( A ^ 1 ) = A

  proof
    cA
    cc
    wcel
    cA
    c1
    cexp
    co
    cA
    wceq
    cA
    numexp.1
    nn0cni
    cA
    exp1
    ax-mp
end
