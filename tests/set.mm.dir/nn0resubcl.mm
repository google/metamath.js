include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "cmin.mm"
include "co.mm"
include "nn0re.mm"
include "resubcl.mm"
include "syl2an.mm"

theorem nn0resubcl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A - B ) e. RR )

  proof
    cA
    cn0
    wcel
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cmin
    co
    cr
    wcel
    cB
    cn0
    wcel
    cA
    nn0re
    cB
    nn0re
    cA
    cB
    resubcl
    syl2an
end
