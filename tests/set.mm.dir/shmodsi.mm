include "wss.mm"
include "cph.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "shseli.mm"
include "cmv.mm"
include "wb.mm"
include "w3a.mm"
include "chil.mm"
include "sheli.mm"
include "hvsubadd.mm"
include "syl3an.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "3expb.mm"
include "shsvsi.mm"
include "shscomi.mm"
include "syl6eleq.mm"
include "shlesb1i.mm"
include "biimpi.mm"
include "eleq2d.mm"
include "syl5ib.mm"
include "eleq1.mm"
include "biimpd.mm"
include "sylan9.mm"
include "anim2d.mm"
include "syl6ibr.mm"
include "ex.mm"
include "com13.mm"
include "ancoms.mm"
include "anasss.mm"
include "sylbird.mm"
include "imp.mm"
include "shincli.mm"
include "shsvai.mm"
include "syl5ibr.mm"
include "expd.mm"
include "com12.mm"
include "ad2antrl.mm"
include "syld.mm"
include "exp31.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "impd.mm"
include "ssrdv.mm"

theorem shmodsi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shmod.1: |- A e. SH
  assume shmod.2: |- B e. SH
  assume shmod.3: |- C e. SH


  assert |- ( A C_ C -> ( ( A +H B ) i^i C ) C_ ( A +H ( B i^i C ) ) )

  proof
    cA
    cC
    wss
    #
    vz
    cA
    cB
    cph
    co
    #
    cC
    cin
    #
    cA
    cB
    cC
    cin
    #
    cph
    co
    #
    vz
    cv
    #
    @2
    wcel
    @5
    @1
    wcel
    #
    @5
    cC
    wcel
    #
    wa
    @0
    @5
    @4
    wcel
    #
    @5
    @1
    cC
    elin
    @0
    @6
    @7
    @8
    @7
    @6
    @0
    @8
    @6
    @5
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @7
    @0
    @8
    wi
    #
    vx
    vy
    cA
    cB
    @5
    shmod.1
    shmod.2
    shseli
    @7
    @12
    @13
    vx
    vy
    cA
    cB
    @7
    @9
    cA
    wcel
    #
    @10
    cB
    wcel
    #
    wa
    #
    @12
    @13
    @7
    @16
    wa
    #
    @12
    wa
    @0
    @10
    @3
    wcel
    #
    @8
    @17
    @12
    @0
    @18
    wi
    #
    @17
    @12
    @5
    @9
    cmv
    co
    #
    @10
    wceq
    #
    @19
    @7
    @14
    @15
    @21
    @12
    wb
    @7
    @14
    @15
    w3a
    @21
    @11
    @5
    wceq
    #
    @12
    @7
    @5
    chil
    wcel
    @14
    @9
    chil
    wcel
    @15
    @10
    chil
    wcel
    @21
    @22
    wb
    @5
    cC
    shmod.3
    sheli
    @9
    cA
    shmod.1
    sheli
    @10
    cB
    shmod.2
    sheli
    @5
    @9
    @10
    hvsubadd
    syl3an
    @11
    @5
    eqcom
    syl6bb
    3expb
    @7
    @14
    @15
    @21
    @19
    wi
    #
    @15
    @7
    @14
    wa
    #
    @23
    @0
    @21
    @15
    @24
    wa
    #
    @18
    @0
    @21
    @25
    @18
    wi
    @0
    @21
    wa
    #
    @25
    @15
    @10
    cC
    wcel
    #
    wa
    @18
    @26
    @24
    @27
    @15
    @0
    @24
    @20
    cC
    wcel
    #
    @21
    @27
    @24
    @20
    cA
    cC
    cph
    co
    #
    wcel
    @0
    @28
    @24
    @20
    cC
    cA
    cph
    co
    @29
    cC
    cA
    @5
    @9
    shmod.3
    shmod.1
    shsvsi
    cC
    cA
    shmod.3
    shmod.1
    shscomi
    syl6eleq
    @0
    @29
    cC
    @20
    @0
    @29
    cC
    wceq
    cA
    cC
    shmod.1
    shmod.3
    shlesb1i
    biimpi
    eleq2d
    syl5ib
    @21
    @28
    @27
    @20
    @10
    cC
    eleq1
    biimpd
    sylan9
    anim2d
    @10
    cB
    cC
    elin
    syl6ibr
    ex
    com13
    ancoms
    anasss
    sylbird
    imp
    @17
    @12
    @18
    @8
    wi
    #
    @14
    @12
    @30
    wi
    @7
    @15
    @12
    @14
    @30
    @12
    @14
    @18
    @8
    @14
    @18
    wa
    @8
    @12
    @11
    @4
    wcel
    cA
    @3
    @9
    @10
    shmod.1
    cB
    cC
    shmod.2
    shmod.3
    shincli
    shsvai
    @5
    @11
    @4
    eleq1
    syl5ibr
    expd
    com12
    ad2antrl
    imp
    syld
    exp31
    rexlimdvv
    syl5bi
    com13
    impd
    syl5bi
    ssrdv
end
