include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "nn0addcl.mm"
include "nn0red.mm"

theorem nn0readdcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A + B ) e. RR )

  proof
    cA
    cn0
    wcel
    cB
    cn0
    wcel
    wa
    cA
    cB
    caddc
    co
    cA
    cB
    nn0addcl
    nn0red
end
