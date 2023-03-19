include "cin.mm"
include "ccv.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "cmd.mm"
include "wcel.mm"
include "anass.mm"
include "chub2i.mm"
include "sstr.mm"
include "mpan2.mm"
include "pm4.71ri.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "wo.mm"
include "chincli.mm"
include "cvnbtwn4.mm"
include "mp3an12.mm"
include "impcom.mm"
include "chjcomi.mm"
include "chabs1i.mm"
include "eqtri.mm"
include "ineq1i.mm"
include "chjidmi.mm"
include "eqtr4i.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "3eqtr4a.mm"
include "incom.mm"
include "chabs2i.mm"
include "oveq2i.mm"
include "3eqtr2i.mm"
include "jaoi.mm"
include "syl6.mm"
include "syl5bi.mm"
include "exp4b.mm"
include "ralrimiv.mm"
include "mdsl1i.mm"
include "sylib.mm"

theorem cvmdi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume mdsl.1: |- A e. CH
  assume mdsl.2: |- B e. CH


  assert |- ( ( A i^i B ) <oH B -> A MH B )

  proof
    cA
    cB
    cin
    #
    cB
    ccv
    wbr
    #
    @0
    vx
    cv
    #
    wss
    #
    @2
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    #
    @2
    cB
    wss
    #
    @2
    cA
    chj
    co
    #
    cB
    cin
    #
    @2
    @0
    chj
    co
    #
    wceq
    #
    wi
    wi
    #
    vx
    cch
    wral
    cA
    cB
    cmd
    wbr
    @1
    @12
    vx
    cch
    @1
    @2
    cch
    wcel
    #
    @6
    @7
    @11
    @6
    @7
    wa
    #
    @3
    @7
    wa
    #
    @1
    @13
    wa
    #
    @11
    @14
    @3
    @5
    @7
    wa
    #
    wa
    @15
    @3
    @5
    @7
    anass
    @7
    @17
    @3
    @7
    @5
    @7
    cB
    @4
    wss
    @5
    cB
    cA
    mdsl.2
    mdsl.1
    chub2i
    @2
    cB
    @4
    sstr
    mpan2
    pm4.71ri
    anbi2i
    bitr4i
    @16
    @15
    @2
    @0
    wceq
    #
    @2
    cB
    wceq
    #
    wo
    #
    @11
    @13
    @1
    @15
    @20
    wi
    #
    @0
    cch
    wcel
    cB
    cch
    wcel
    @13
    @1
    @21
    wi
    cA
    cB
    mdsl.1
    mdsl.2
    chincli
    #
    mdsl.2
    @0
    cB
    @2
    cvnbtwn4
    mp3an12
    impcom
    @18
    @11
    @19
    @18
    @0
    cA
    chj
    co
    #
    cB
    cin
    #
    @0
    @0
    chj
    co
    #
    @9
    @10
    @24
    @0
    @25
    @23
    cA
    cB
    @23
    cA
    @0
    chj
    co
    cA
    @0
    cA
    @22
    mdsl.1
    chjcomi
    cA
    cB
    mdsl.1
    mdsl.2
    chabs1i
    eqtri
    ineq1i
    @0
    @22
    chjidmi
    eqtr4i
    @18
    @8
    @23
    cB
    @2
    @0
    cA
    chj
    oveq1
    ineq1d
    @2
    @0
    @0
    chj
    oveq1
    3eqtr4a
    @19
    cB
    cA
    chj
    co
    #
    cB
    cin
    #
    cB
    @0
    chj
    co
    #
    @9
    @10
    @27
    cB
    @26
    cin
    #
    @28
    @26
    cB
    incom
    @29
    cB
    cB
    cB
    cA
    cin
    #
    chj
    co
    @28
    cB
    cA
    mdsl.2
    mdsl.1
    chabs2i
    cB
    cA
    mdsl.2
    mdsl.1
    chabs1i
    @30
    @0
    cB
    chj
    cB
    cA
    incom
    oveq2i
    3eqtr2i
    eqtri
    @19
    @8
    @26
    cB
    @2
    cB
    cA
    chj
    oveq1
    ineq1d
    @2
    cB
    @0
    chj
    oveq1
    3eqtr4a
    jaoi
    syl6
    syl5bi
    exp4b
    ralrimiv
    vx
    cA
    cB
    mdsl.1
    mdsl.2
    mdsl1i
    sylib
end
