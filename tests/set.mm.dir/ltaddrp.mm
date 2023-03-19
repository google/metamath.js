include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "elrp.mm"
include "wi.mm"
include "ltaddpos.mm"
include "biimpd.mm"
include "expcom.mm"
include "imp32.mm"
include "sylan2b.mm"

theorem ltaddrp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> A < ( A + B ) )

  proof
    cB
    crp
    wcel
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    cA
    cA
    cB
    caddc
    co
    clt
    wbr
    #
    cB
    elrp
    @0
    @1
    @2
    @3
    @1
    @0
    @2
    @3
    wi
    @1
    @0
    wa
    @2
    @3
    cB
    cA
    ltaddpos
    biimpd
    expcom
    imp32
    sylan2b
end
