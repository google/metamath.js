include "cn0.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "faccl.mm"
include "nnne0d.mm"

theorem facne0
  let cN: class N


  assert |- ( N e. NN0 -> ( ! ` N ) =/= 0 )

  proof
    cN
    cn0
    wcel
    cN
    cfa
    cfv
    cN
    faccl
    nnne0d
end
