include "co.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cdm.mm"
include "df-br.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "wn.mm"
include "cfv.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "necon1ai.mm"
include "syl.mm"
include "sylbi.mm"

theorem brovpreldm
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( D ( B A C ) E -> <. B , C >. e. dom A )

  proof
    cD
    cE
    cB
    cC
    cA
    co
    #
    wbr
    cD
    cE
    cop
    #
    @0
    wcel
    #
    cB
    cC
    cop
    #
    cA
    cdm
    wcel
    #
    cD
    cE
    @0
    df-br
    @2
    @0
    c0
    wne
    @4
    @0
    @1
    ne0i
    @4
    @0
    c0
    @4
    wn
    @0
    @3
    cA
    cfv
    c0
    cB
    cC
    cA
    df-ov
    @3
    cA
    ndmfv
    syl5eq
    necon1ai
    syl
    sylbi
end
