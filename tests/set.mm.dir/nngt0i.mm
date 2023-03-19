include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "nngt0.mm"
include "ax-mp.mm"

theorem nngt0i
  let cA: class A
  assume nngt0.1: |- A e. NN


  assert |- 0 < A

  proof
    cA
    cn
    wcel
    cc0
    cA
    clt
    wbr
    nngt0.1
    cA
    nngt0
    ax-mp
end
