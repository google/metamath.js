include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "ge0div.mm"
include "biimpd.mm"
include "3exp.mm"
include "com34.mm"
include "com23.mm"
include "imp43.mm"

theorem divge0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 < B ) ) -> 0 <_ ( A / B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
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
    cle
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
    ge0div
    biimpd
    3exp
    com34
    com23
    imp43
end
