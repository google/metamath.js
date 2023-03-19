include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cn.mm"
include "eedimeq.mm"
include "ad2ant2l.mm"

theorem axdimuniq
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) ) /\ ( M e. NN /\ A e. ( EE ` M ) ) ) -> N = M )

  proof
    cA
    cN
    cee
    cfv
    wcel
    cA
    cM
    cee
    cfv
    wcel
    cN
    cM
    wceq
    cN
    cn
    wcel
    cM
    cn
    wcel
    cA
    cM
    cN
    eedimeq
    ad2ant2l
end
