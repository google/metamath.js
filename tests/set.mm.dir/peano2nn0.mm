include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "1nn0.mm"
include "nn0addcl.mm"
include "mpan2.mm"

theorem peano2nn0
  let cN: class N


  assert |- ( N e. NN0 -> ( N + 1 ) e. NN0 )

  proof
    cN
    cn0
    wcel
    c1
    cn0
    wcel
    cN
    c1
    caddc
    co
    cn0
    wcel
    1nn0
    cN
    c1
    nn0addcl
    mpan2
end
