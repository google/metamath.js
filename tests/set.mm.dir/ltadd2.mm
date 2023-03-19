include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "axltadd.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "oveq2.mm"
include "a1i.mm"
include "3com12.mm"
include "orim12d.mm"
include "con3d.mm"
include "wb.mm"
include "simp3.mm"
include "simp1.mm"
include "readdcld.mm"
include "simp2.mm"
include "axlttri.mm"
include "syl2anc.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem ltadd2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A < B <-> ( C + A ) < ( C + B ) ) )

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
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cC
    cA
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    clt
    wbr
    #
    cA
    cB
    cC
    axltadd
    @3
    @5
    @6
    wceq
    #
    @6
    @5
    clt
    wbr
    #
    wo
    #
    wn
    #
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
    #
    @7
    @4
    @3
    @14
    @10
    @3
    @12
    @8
    @13
    @9
    @12
    @8
    wi
    @3
    cA
    cB
    cC
    caddc
    oveq2
    a1i
    @1
    @0
    @2
    @13
    @9
    wi
    cB
    cA
    cC
    axltadd
    3com12
    orim12d
    con3d
    @3
    @5
    cr
    wcel
    @6
    cr
    wcel
    @7
    @11
    wb
    @3
    cC
    cA
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp1
    #
    readdcld
    @3
    cC
    cB
    @16
    @0
    @1
    @2
    simp2
    #
    readdcld
    @5
    @6
    axlttri
    syl2anc
    @3
    @0
    @1
    @4
    @15
    wb
    @17
    @18
    cA
    cB
    axlttri
    syl2anc
    3imtr4d
    impbid
end
