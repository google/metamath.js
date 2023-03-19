include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "ltmul1a.mm"
include "ex.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "oveq1.mm"
include "a1i.mm"
include "3com12.mm"
include "orim12d.mm"
include "con3d.mm"
include "simp1.mm"
include "simp3l.mm"
include "remulcld.mm"
include "simp2.mm"
include "lttrid.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem ltmul1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( A < B <-> ( A x. C ) < ( B x. C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    clt
    wbr
    #
    @5
    @6
    @9
    cA
    cB
    cC
    ltmul1a
    ex
    @5
    @7
    @8
    wceq
    #
    @8
    @7
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
    @9
    @6
    @5
    @15
    @12
    @5
    @13
    @10
    @14
    @11
    @13
    @10
    wi
    @5
    cA
    cB
    cC
    cmul
    oveq1
    a1i
    @1
    @0
    @4
    @14
    @11
    wi
    @1
    @0
    @4
    w3a
    @14
    @11
    cB
    cA
    cC
    ltmul1a
    ex
    3com12
    orim12d
    con3d
    @5
    @7
    @8
    @5
    cA
    cC
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @2
    @3
    simp3l
    #
    remulcld
    @5
    cB
    cC
    @0
    @1
    @4
    simp2
    #
    @17
    remulcld
    lttrid
    @5
    cA
    cB
    @16
    @18
    lttrid
    3imtr4d
    impbid
end
