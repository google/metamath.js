include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "ltle.mm"
include "ad2ant2r.mm"
include "leltadd.mm"
include "syland.mm"

theorem lt2add
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A < C /\ B < D ) -> ( A + B ) < ( C + D ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    wa
    cA
    cC
    clt
    wbr
    #
    cA
    cC
    cle
    wbr
    #
    cB
    cD
    clt
    wbr
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    clt
    wbr
    @0
    @2
    @4
    @5
    wi
    @1
    @3
    cA
    cC
    ltle
    ad2ant2r
    cA
    cB
    cC
    cD
    leltadd
    syland
end
