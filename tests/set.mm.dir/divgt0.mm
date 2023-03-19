include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "gt0div.mm"
include "biimpd.mm"
include "3exp.mm"
include "com34.mm"
include "com23.mm"
include "imp43.mm"

theorem divgt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) -> 0 < ( A / B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
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
    cc0
    cA
    cB
    cdiv
    co
    clt
    wbr
    #
    @0
    @2
    @1
    @3
    @4
    wi
    @0
    @2
    @3
    @1
    @4
    @0
    @2
    @3
    @1
    @4
    wi
    @0
    @2
    @3
    w3a
    @1
    @4
    cA
    cB
    gt0div
    biimpd
    3exp
    com34
    com23
    imp43
end
