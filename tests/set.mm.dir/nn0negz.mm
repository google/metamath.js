include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cneg.mm"
include "nn0z.mm"
include "znegcl.mm"
include "syl.mm"

theorem nn0negz
  let cN: class N


  assert |- ( N e. NN0 -> -u N e. ZZ )

  proof
    cN
    cn0
    wcel
    cN
    cz
    wcel
    cN
    cneg
    cz
    wcel
    cN
    nn0z
    cN
    znegcl
    syl
end
