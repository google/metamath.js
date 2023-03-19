include "c1.mm"
include "cn.mm"
include "nnuz.mm"
include "uztrn2.mm"

theorem eluznn
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN /\ M e. ( ZZ>= ` N ) ) -> M e. NN )

  proof
    c1
    cM
    cN
    cn
    nnuz
    uztrn2
end
