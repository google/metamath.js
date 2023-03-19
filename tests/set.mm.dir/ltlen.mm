include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wne.mm"
include "ltle.mm"
include "wi.mm"
include "ltne.mm"
include "ex.mm"
include "adantr.mm"
include "jcad.mm"
include "wceq.mm"
include "wo.mm"
include "leloe.mm"
include "ax-1.mm"
include "wn.mm"
include "df-ne.mm"
include "pm2.24.mm"
include "eqcoms.mm"
include "syl5bi.mm"
include "jaoi.mm"
include "syl6bi.mm"
include "impd.mm"
include "impbid.mm"

theorem ltlen
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> ( A <_ B /\ B =/= A ) ) )

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
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    wne
    #
    wa
    @2
    @3
    @4
    @5
    cA
    cB
    ltle
    @0
    @3
    @5
    wi
    @1
    @0
    @3
    @5
    cA
    cB
    ltne
    ex
    adantr
    jcad
    @2
    @4
    @5
    @3
    @2
    @4
    @3
    cA
    cB
    wceq
    #
    wo
    @5
    @3
    wi
    #
    cA
    cB
    leloe
    @3
    @7
    @6
    @3
    @5
    ax-1
    @5
    cB
    cA
    wceq
    #
    wn
    #
    @6
    @3
    cB
    cA
    df-ne
    @9
    @3
    wi
    cB
    cA
    @8
    @3
    pm2.24
    eqcoms
    syl5bi
    jaoi
    syl6bi
    impd
    impbid
end
