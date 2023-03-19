include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "ltnr.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"

theorem ltne
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ A < B ) -> B =/= A )

  proof
    cA
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    wne
    @0
    @1
    cB
    cA
    @0
    @1
    wn
    cB
    cA
    wceq
    #
    cA
    cA
    clt
    wbr
    #
    wn
    cA
    ltnr
    @2
    @1
    @3
    cB
    cA
    cA
    clt
    breq2
    notbid
    syl5ibrcom
    necon2ad
    imp
end
