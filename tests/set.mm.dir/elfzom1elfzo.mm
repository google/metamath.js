include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "fzossrbm1.mm"
include "sselda.mm"

theorem elfzom1elfzo
  let cI: class I
  let cN: class N


  assert |- ( ( N e. ZZ /\ I e. ( 0 ..^ ( N - 1 ) ) ) -> I e. ( 0 ..^ N ) )

  proof
    cN
    cz
    wcel
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    cc0
    cN
    cfzo
    co
    cI
    cN
    fzossrbm1
    sselda
end
