include "cc0.mm"
include "cdp2.mm"
include "crp.mm"
include "nnnn0i.mm"
include "dp20u.mm"
include "cn.mm"
include "wcel.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem rpdp2cl2
  let cA: class A
  assume rpdp2cl2.a: |- A e. NN


  assert |- _ A 0 e. RR+

  proof
    cA
    cc0
    cdp2
    cA
    crp
    cA
    cA
    rpdp2cl2.a
    nnnn0i
    dp20u
    cA
    cn
    wcel
    cA
    crp
    wcel
    rpdp2cl2.a
    cA
    nnrp
    ax-mp
    eqeltri
end
