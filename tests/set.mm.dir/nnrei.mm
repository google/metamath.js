include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "nnre.mm"
include "ax-mp.mm"

theorem nnrei
  let cA: class A
  assume nnre.1: |- A e. NN


  assert |- A e. RR

  proof
    cA
    cn
    wcel
    cA
    cr
    wcel
    nnre.1
    cA
    nnre
    ax-mp
end
