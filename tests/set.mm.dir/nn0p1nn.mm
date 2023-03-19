include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cn.mm"
include "caddc.mm"
include "co.mm"
include "1nn.mm"
include "nn0nnaddcl.mm"
include "mpan2.mm"

theorem nn0p1nn
  let cN: class N


  assert |- ( N e. NN0 -> ( N + 1 ) e. NN )

  proof
    cN
    cn0
    wcel
    c1
    cn
    wcel
    cN
    c1
    caddc
    co
    cn
    wcel
    1nn
    cN
    c1
    nn0nnaddcl
    mpan2
end
