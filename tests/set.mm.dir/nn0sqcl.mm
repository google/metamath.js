include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "2nn0.mm"
include "nn0expcl.mm"
include "mpan2.mm"

theorem nn0sqcl
  let cA: class A


  assert |- ( A e. NN0 -> ( A ^ 2 ) e. NN0 )

  proof
    cA
    cn0
    wcel
    c2
    cn0
    wcel
    cA
    c2
    cexp
    co
    cn0
    wcel
    2nn0
    cA
    c2
    nn0expcl
    mpan2
end
