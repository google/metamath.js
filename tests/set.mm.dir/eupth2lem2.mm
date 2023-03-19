include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "eqidd.mm"
include "olcd.mm"
include "biantrud.mm"
include "cvv.mm"
include "wb.mm"
include "eupth2lem1.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "simpr.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "necon1bbid.mm"
include "simpl.mm"
include "neeq1.mm"
include "syl5ibcom.mm"
include "pm4.71rd.mm"
include "eqcom.mm"
include "ancom.mm"
include "3bitr4g.mm"
include "neneqd.mm"
include "biorf.mm"
include "syl.mm"
include "orcom.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "syl5bbr.mm"
include "3bitrd.mm"

theorem eupth2lem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  assume eupth2lem2.1: |- B e. _V


  assert |- ( ( B =/= C /\ B = U ) -> ( -. U e. if ( A = B , (/) , { A , B } ) <-> U e. if ( A = C , (/) , { A , C } ) ) )

  proof
    cB
    cC
    wne
    #
    cB
    cU
    wceq
    #
    wa
    #
    cU
    cA
    cB
    wceq
    #
    c0
    cA
    cB
    cpr
    cif
    #
    wcel
    #
    wn
    @3
    cA
    cC
    wne
    #
    cB
    cA
    wceq
    #
    cB
    cC
    wceq
    #
    wo
    #
    wa
    #
    cU
    cA
    cC
    wceq
    c0
    cA
    cC
    cpr
    cif
    #
    wcel
    #
    @2
    @5
    cA
    cB
    @2
    cA
    cB
    wne
    #
    cB
    @4
    wcel
    #
    @5
    @2
    @13
    @13
    @7
    cB
    cB
    wceq
    #
    wo
    #
    wa
    #
    @14
    @2
    @16
    @13
    @2
    @15
    @7
    @2
    cB
    eqidd
    olcd
    biantrud
    cB
    cvv
    wcel
    #
    @14
    @17
    wb
    eupth2lem2.1
    cA
    cB
    cB
    cvv
    eupth2lem1
    ax-mp
    syl6bbr
    @2
    cB
    cU
    @4
    @0
    @1
    simpr
    #
    eleq1d
    bitrd
    necon1bbid
    @2
    @3
    @9
    @6
    wa
    #
    @10
    @2
    @3
    @7
    @6
    wa
    #
    @20
    @2
    @7
    @6
    @7
    wa
    @3
    @21
    @2
    @7
    @6
    @2
    @0
    @7
    @6
    @0
    @1
    simpl
    #
    cB
    cA
    cC
    neeq1
    syl5ibcom
    pm4.71rd
    cA
    cB
    eqcom
    @7
    @6
    ancom
    3bitr4g
    @2
    @7
    @9
    @6
    @2
    @7
    @8
    @7
    wo
    #
    @9
    @2
    @8
    wn
    @7
    @23
    wb
    @2
    cB
    cC
    @22
    neneqd
    @8
    @7
    biorf
    syl
    @8
    @7
    orcom
    syl6bb
    anbi1d
    bitrd
    @6
    @9
    ancom
    syl6bbr
    @10
    cB
    @11
    wcel
    #
    @2
    @12
    @18
    @24
    @10
    wb
    eupth2lem2.1
    cA
    cC
    cB
    cvv
    eupth2lem1
    ax-mp
    @2
    cB
    cU
    @11
    @19
    eleq1d
    syl5bbr
    3bitrd
end
