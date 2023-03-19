include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "word.mm"
include "wtr.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "csn.mm"
include "wo.mm"
include "onelss.mm"
include "wi.mm"
include "wceq.mm"
include "velsn.mm"
include "eqimss.mm"
include "sylbi.mm"
include "a1i.mm"
include "orim12d.mm"
include "cun.mm"
include "df-suc.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr2i.mm"
include "oridm.mm"
include "3imtr3g.mm"
include "sssucid.mm"
include "sstr2.mm"
include "syl6mpi.mm"
include "ralrimiv.mm"
include "dftr3.mm"
include "sylibr.mm"
include "onss.mm"
include "snssi.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "ordon.mm"
include "trssord.mm"
include "3exp.mm"
include "mpii.mm"
include "sylc.mm"
include "cvv.mm"
include "wb.mm"
include "sucexg.mm"
include "elong.mm"
include "syl.mm"
include "mpbird.mm"

theorem suceloni
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> suc A e. On )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    con0
    wcel
    #
    @1
    word
    #
    @0
    @1
    wtr
    #
    @1
    con0
    wss
    #
    @3
    @0
    vx
    cv
    #
    @1
    wss
    #
    vx
    @1
    wral
    @4
    @0
    @7
    vx
    @1
    @0
    @6
    @1
    wcel
    #
    @6
    cA
    wss
    #
    cA
    @1
    wss
    @7
    @0
    @6
    cA
    wcel
    #
    @6
    cA
    csn
    #
    wcel
    #
    wo
    #
    @9
    @9
    wo
    @8
    @9
    @0
    @10
    @9
    @12
    @9
    cA
    @6
    onelss
    @12
    @9
    wi
    @0
    @12
    @6
    cA
    wceq
    @9
    vx
    cA
    velsn
    @6
    cA
    eqimss
    sylbi
    a1i
    orim12d
    @8
    @6
    cA
    @11
    cun
    #
    wcel
    @13
    @1
    @14
    @6
    cA
    df-suc
    #
    eleq2i
    @6
    cA
    @11
    elun
    bitr2i
    @9
    oridm
    3imtr3g
    cA
    sssucid
    @6
    cA
    @1
    sstr2
    syl6mpi
    ralrimiv
    vx
    @1
    dftr3
    sylibr
    @0
    @1
    @14
    con0
    @15
    @0
    cA
    @11
    con0
    cA
    onss
    cA
    con0
    snssi
    unssd
    syl5eqss
    @4
    @5
    con0
    word
    #
    @3
    ordon
    @4
    @5
    @16
    @3
    @1
    con0
    trssord
    3exp
    mpii
    sylc
    @0
    @1
    cvv
    wcel
    @2
    @3
    wb
    cA
    con0
    sucexg
    @1
    cvv
    elong
    syl
    mpbird
end
