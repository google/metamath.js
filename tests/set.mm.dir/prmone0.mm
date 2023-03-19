include "cn0.mm"
include "wcel.mm"
include "cprmo.mm"
include "cfv.mm"
include "prmocl.mm"
include "nnne0d.mm"

theorem prmone0
  let cN: class N


  assert |- ( N e. NN0 -> ( #p ` N ) =/= 0 )

  proof
    cN
    cn0
    wcel
    cN
    cprmo
    cfv
    cN
    prmocl
    nnne0d
end
