include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wne.mm"
include "wb.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "lttri3.mm"
include "simpl.mm"
include "syl6bi.mm"
include "adantr.mm"
include "wo.mm"
include "leloe.mm"
include "biimpa.mm"
include "ord.mm"
include "impbid.mm"
include "necon2abid.mm"
include "necom.mm"
include "syl6bbr.mm"
include "3impa.mm"

theorem leltne
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( A < B <-> B =/= A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    wne
    #
    wb
    @0
    @1
    wa
    #
    @2
    wa
    #
    @3
    cA
    cB
    wne
    @4
    @6
    @3
    cA
    cB
    @6
    cA
    cB
    wceq
    #
    @3
    wn
    #
    @5
    @7
    @8
    wi
    @2
    @5
    @7
    @8
    cB
    cA
    clt
    wbr
    wn
    #
    wa
    @8
    cA
    cB
    lttri3
    @8
    @9
    simpl
    syl6bi
    adantr
    @6
    @3
    @7
    @5
    @2
    @3
    @7
    wo
    cA
    cB
    leloe
    biimpa
    ord
    impbid
    necon2abid
    cB
    cA
    necom
    syl6bbr
    3impa
end
