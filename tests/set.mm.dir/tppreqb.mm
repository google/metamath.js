include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wn.mm"
include "ctp.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "3ianor.mm"
include "df-3or.mm"
include "bitri.mm"
include "orass.mm"
include "wa.mm"
include "ianor.mm"
include "tpprceq3.mm"
include "sylbir.mm"
include "tpcoma.mm"
include "prcom.mm"
include "3eqtr3g.mm"
include "orcom.mm"
include "bitr4i.mm"
include "sylbi.mm"
include "jaoi.mm"
include "orcs.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "eqeq1i.mm"
include "wss.mm"
include "ssequn2.mm"
include "wi.mm"
include "snssg.mm"
include "elpri.mm"
include "nne.mm"
include "3mix2.mm"
include "3mix3.mm"
include "syl.mm"
include "syl6bir.mm"
include "3mix1.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "sylibr.mm"
include "impbii.mm"

theorem tppreqb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. ( C e. _V /\ C =/= A /\ C =/= B ) <-> { A , B , C } = { A , B } )

  proof
    cC
    cvv
    wcel
    #
    cC
    cA
    wne
    #
    cC
    cB
    wne
    #
    w3a
    wn
    #
    cA
    cB
    cC
    ctp
    #
    cA
    cB
    cpr
    #
    wceq
    #
    @3
    @0
    wn
    #
    @1
    wn
    #
    wo
    #
    @2
    wn
    #
    wo
    #
    @6
    @3
    @7
    @8
    @10
    w3o
    #
    @11
    @0
    @1
    @2
    3ianor
    #
    @7
    @8
    @10
    df-3or
    bitri
    @11
    @7
    @6
    @11
    @7
    wo
    @9
    @10
    @7
    wo
    #
    wo
    @6
    @9
    @10
    @7
    orass
    @9
    @6
    @14
    @9
    cB
    cA
    cC
    ctp
    #
    cB
    cA
    cpr
    #
    @4
    @5
    @9
    @0
    @1
    wa
    wn
    @15
    @16
    wceq
    @0
    @1
    ianor
    cB
    cA
    cC
    tpprceq3
    sylbir
    cB
    cA
    cC
    tpcoma
    cB
    cA
    prcom
    3eqtr3g
    @14
    @0
    @2
    wa
    wn
    #
    @6
    @14
    @7
    @10
    wo
    @17
    @10
    @7
    orcom
    @0
    @2
    ianor
    bitr4i
    cA
    cB
    cC
    tpprceq3
    sylbi
    jaoi
    sylbi
    orcs
    sylbi
    @6
    @5
    cC
    csn
    #
    cun
    #
    @5
    wceq
    #
    @3
    @4
    @19
    @5
    cA
    cB
    cC
    df-tp
    eqeq1i
    @20
    @18
    @5
    wss
    #
    @3
    @18
    @5
    ssequn2
    @21
    @12
    @3
    @0
    @21
    @12
    wi
    @0
    @21
    cC
    @5
    wcel
    #
    @12
    cC
    @5
    cvv
    snssg
    @22
    cC
    cA
    wceq
    #
    cC
    cB
    wceq
    #
    wo
    @12
    cC
    cA
    cB
    elpri
    @23
    @12
    @24
    @23
    @8
    @12
    cC
    cA
    nne
    @8
    @7
    @10
    3mix2
    sylbir
    @24
    @10
    @12
    cC
    cB
    nne
    @10
    @7
    @8
    3mix3
    sylbir
    jaoi
    syl
    syl6bir
    @7
    @12
    @21
    @7
    @8
    @10
    3mix1
    a1d
    pm2.61i
    @13
    sylibr
    sylbir
    sylbi
    impbii
end
