include "com.mm"
include "wcel.mm"
include "csdm.mm"
include "wbr.mm"
include "csuc.mm"
include "cdom.mm"
include "sucdom2.mm"
include "wi.mm"
include "php4.mm"
include "sdomdomtr.mm"
include "ex.mm"
include "syl.mm"
include "impbid2.mm"

theorem sucdom
  let cA: class A
  let cB: class B


  assert |- ( A e. _om -> ( A ~< B <-> suc A ~<_ B ) )

  proof
    cA
    com
    wcel
    #
    cA
    cB
    csdm
    wbr
    #
    cA
    csuc
    #
    cB
    cdom
    wbr
    #
    cA
    cB
    sucdom2
    @0
    cA
    @2
    csdm
    wbr
    #
    @3
    @1
    wi
    cA
    php4
    @4
    @3
    @1
    cA
    @2
    cB
    sdomdomtr
    ex
    syl
    impbid2
end
