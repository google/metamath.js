include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "csdm.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelexi.mm"
include "nnsdomg.mm"
include "sylan.mm"
include "simpl.mm"
include "sdomdomtr.mm"
include "syl2anc.mm"

theorem infsdomnn
  let cA: class A
  let cB: class B


  assert |- ( ( _om ~<_ A /\ B e. _om ) -> B ~< A )

  proof
    com
    cA
    cdom
    wbr
    #
    cB
    com
    wcel
    #
    wa
    cB
    com
    csdm
    wbr
    #
    @0
    cB
    cA
    csdm
    wbr
    @0
    com
    cvv
    wcel
    @1
    @2
    com
    cA
    cdom
    reldom
    brrelexi
    cB
    nnsdomg
    sylan
    @0
    @1
    simpl
    cB
    com
    cA
    sdomdomtr
    syl2anc
end
