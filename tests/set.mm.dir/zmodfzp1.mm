include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cfz.mm"
include "cmo.mm"
include "fzossfz.mm"
include "zmodfzo.mm"
include "sseldi.mm"

theorem zmodfzp1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) e. ( 0 ... B ) )

  proof
    cA
    cz
    wcel
    cB
    cn
    wcel
    wa
    cc0
    cB
    cfzo
    co
    cc0
    cB
    cfz
    co
    cA
    cB
    cmo
    co
    cc0
    cB
    fzossfz
    cA
    cB
    zmodfzo
    sseldi
end
