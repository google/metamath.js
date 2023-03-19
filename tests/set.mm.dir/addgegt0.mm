include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "00id.mm"
include "wi.mm"
include "0re.mm"
include "leltadd.mm"
include "mpanl12.mm"
include "imp.mm"
include "syl5eqbrr.mm"

theorem addgegt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ 0 < B ) ) -> 0 < ( A + B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cc0
    cA
    cle
    wbr
    cc0
    cB
    clt
    wbr
    wa
    #
    wa
    cc0
    cc0
    cc0
    caddc
    co
    #
    cA
    cB
    caddc
    co
    #
    clt
    00id
    @0
    @1
    @2
    @3
    clt
    wbr
    #
    cc0
    cr
    wcel
    #
    @5
    @0
    @1
    @4
    wi
    0re
    0re
    cc0
    cc0
    cA
    cB
    leltadd
    mpanl12
    imp
    syl5eqbrr
end
