include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "00id.mm"
include "wi.mm"
include "0re.mm"
include "le2add.mm"
include "mpanl12.mm"
include "imp.mm"
include "syl5eqbrr.mm"

theorem addge0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ 0 <_ B ) ) -> 0 <_ ( A + B ) )

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
    cle
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
    cle
    00id
    @0
    @1
    @2
    @3
    cle
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
    le2add
    mpanl12
    imp
    syl5eqbrr
end
