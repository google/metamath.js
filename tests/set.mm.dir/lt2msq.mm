include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "lt2msq1.mm"
include "3expia.mm"
include "adantrr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "id.mm"
include "oveq12d.mm"
include "a1i.mm"
include "ancoms.mm"
include "orim12d.mm"
include "con3d.mm"
include "simpll.mm"
include "remulcld.mm"
include "simprl.mm"
include "lttrid.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem lt2msq
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( A < B <-> ( A x. A ) < ( B x. B ) ) )

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
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @3
    @7
    @10
    wi
    @4
    @2
    @3
    @7
    @10
    cA
    cB
    lt2msq1
    3expia
    adantrr
    @6
    @8
    @9
    wceq
    #
    @9
    @8
    clt
    wbr
    #
    wo
    #
    wn
    cA
    cB
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    wo
    #
    wn
    @10
    @7
    @6
    @16
    @13
    @6
    @14
    @11
    @15
    @12
    @14
    @11
    wi
    @6
    @14
    cA
    cB
    cA
    cB
    cmul
    @14
    id
    #
    @17
    oveq12d
    a1i
    @5
    @2
    @15
    @12
    wi
    #
    @5
    @0
    @18
    @1
    @5
    @0
    @15
    @12
    cB
    cA
    lt2msq1
    3expia
    adantrr
    ancoms
    orim12d
    con3d
    @6
    @8
    @9
    @6
    cA
    cA
    @0
    @1
    @5
    simpll
    #
    @19
    remulcld
    @6
    cB
    cB
    @2
    @3
    @4
    simprl
    #
    @20
    remulcld
    lttrid
    @6
    cA
    cB
    @19
    @20
    lttrid
    3imtr4d
    impbid
end
