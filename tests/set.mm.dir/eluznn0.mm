include "cc0.mm"
include "cn0.mm"
include "nn0uz.mm"
include "uztrn2.mm"

theorem eluznn0
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN0 /\ M e. ( ZZ>= ` N ) ) -> M e. NN0 )

  proof
    cc0
    cM
    cN
    cn0
    nn0uz
    uztrn2
end
