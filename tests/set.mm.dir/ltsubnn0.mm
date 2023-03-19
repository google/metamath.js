include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "wi.mm"
include "nn0re.mm"
include "ltle.mm"
include "syl2anr.mm"
include "wb.mm"
include "nn0sub.mm"
include "ancoms.mm"
include "sylibd.mm"

theorem ltsubnn0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( B < A -> ( A - B ) e. NN0 ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    cB
    cA
    clt
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    cA
    cB
    cmin
    co
    cn0
    wcel
    #
    @1
    cB
    cr
    wcel
    cA
    cr
    wcel
    @2
    @3
    wi
    @0
    cB
    nn0re
    cA
    nn0re
    cB
    cA
    ltle
    syl2anr
    @1
    @0
    @3
    @4
    wb
    cB
    cA
    nn0sub
    ancoms
    sylibd
end
