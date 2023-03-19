include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "elrp.mm"
include "wi.mm"
include "ltsubpos.mm"
include "biimpd.mm"
include "expcom.mm"
include "imp32.mm"
include "sylan2b.mm"

theorem ltsubrp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A - B ) < A )

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
    cB
    cmin
    co
    cA
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
    ltsubpos
    biimpd
    expcom
    imp32
    sylan2b
end
