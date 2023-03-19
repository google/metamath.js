include "clvec.mm"
include "clmod.mm"
include "bj-vecssmod.mm"
include "sseli.mm"

theorem bj-vecssmodel
  let cA: class A


  assert |- ( A e. LVec -> A e. LMod )

  proof
    clvec
    clmod
    cA
    bj-vecssmod
    sseli
end
