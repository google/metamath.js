include "cv.mm"
include "wss.mm"
include "cin.mm"
include "wn.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "ccv.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "cch.mm"
include "wcel.mm"
include "wi.mm"
include "chincli.mm"
include "cvpss.mm"
include "mp2an.mm"
include "chpssati.mm"
include "syl.mm"
include "ssin.mm"
include "ancom.mm"
include "bitr3i.mm"
include "baibr.mm"
include "notbid.mm"
include "biimpar.mm"
include "wb.mm"
include "chcv1.mm"
include "mpan.mm"
include "biimpa.mm"
include "sylan2.mm"
include "adantrr.mm"
include "wceq.mm"
include "atelch.mm"
include "chabs1i.mm"
include "oveq1i.mm"
include "chjass.mm"
include "mp3an12.mm"
include "syl5reqr.mm"
include "adantr.mm"
include "chnle.mm"
include "inss2.mm"
include "biantrur.mm"
include "chlub.mm"
include "mp3an13.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "chjcl.mm"
include "cvnbtwn2.mm"
include "com23.mm"
include "sylbid.mm"
include "imp32.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "sylan.mm"
include "breqtrd.mm"
include "exp32.mm"
include "rexlimiv.mm"
include "mpcom.mm"

theorem cvexchlem
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH


  assert |- ( ( A i^i B ) <oH B -> A <oH ( A vH B ) )

  proof
    vx
    cv
    #
    cB
    wss
    #
    @0
    cA
    cB
    cin
    #
    wss
    #
    wn
    #
    wa
    #
    vx
    cat
    wrex
    #
    @2
    cB
    ccv
    wbr
    #
    cA
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    @7
    @2
    cB
    wpss
    #
    @6
    @2
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @7
    @10
    wi
    cA
    cB
    chpssat.1
    chpssat.2
    chincli
    #
    chpssat.2
    @2
    cB
    cvpss
    mp2an
    vx
    @2
    cB
    @13
    chpssat.2
    chpssati
    syl
    @5
    @7
    @9
    wi
    vx
    cat
    @0
    cat
    wcel
    #
    @5
    @7
    @9
    @14
    @5
    @7
    wa
    #
    wa
    cA
    cA
    @0
    chj
    co
    #
    @8
    ccv
    @14
    @5
    cA
    @16
    ccv
    wbr
    #
    @7
    @5
    @14
    @0
    cA
    wss
    #
    wn
    #
    @17
    @1
    @19
    @4
    @1
    @18
    @3
    @3
    @1
    @18
    @3
    @18
    @1
    wa
    @1
    @18
    wa
    @0
    cA
    cB
    ssin
    @18
    @1
    ancom
    bitr3i
    baibr
    notbid
    biimpar
    @14
    @19
    @17
    cA
    cch
    wcel
    #
    @14
    @19
    @17
    wb
    chpssat.1
    cA
    @0
    chcv1
    mpan
    biimpa
    sylan2
    adantrr
    @14
    @0
    cch
    wcel
    #
    @15
    @16
    @8
    wceq
    @0
    atelch
    @21
    @15
    wa
    #
    cA
    @2
    @0
    chj
    co
    #
    chj
    co
    #
    @16
    @8
    @21
    @24
    @16
    wceq
    @15
    @21
    @16
    cA
    @2
    chj
    co
    #
    @0
    chj
    co
    #
    @24
    @25
    cA
    @0
    chj
    cA
    cB
    chpssat.1
    chpssat.2
    chabs1i
    oveq1i
    @20
    @11
    @21
    @26
    @24
    wceq
    chpssat.1
    @13
    cA
    @2
    @0
    chjass
    mp3an12
    syl5reqr
    adantr
    @22
    @23
    cB
    cA
    chj
    @21
    @5
    @7
    @23
    cB
    wceq
    #
    @21
    @5
    @2
    @23
    wpss
    #
    @23
    cB
    wss
    #
    wa
    #
    @7
    @27
    wi
    @5
    @4
    @1
    wa
    @21
    @30
    @1
    @4
    ancom
    @21
    @4
    @28
    @1
    @29
    @11
    @21
    @4
    @28
    wb
    @13
    @2
    @0
    chnle
    mpan
    @1
    @2
    cB
    wss
    #
    @1
    wa
    #
    @21
    @29
    @31
    @1
    cA
    cB
    inss2
    biantrur
    @11
    @21
    @12
    @32
    @29
    wb
    @13
    chpssat.2
    @2
    @0
    cB
    chlub
    mp3an13
    syl5bb
    anbi12d
    syl5bb
    @21
    @7
    @30
    @27
    @21
    @23
    cch
    wcel
    #
    @7
    @30
    @27
    wi
    wi
    #
    @11
    @21
    @33
    @13
    @2
    @0
    chjcl
    mpan
    @11
    @12
    @33
    @34
    @13
    chpssat.2
    @2
    cB
    @23
    cvnbtwn2
    mp3an12
    syl
    com23
    sylbid
    imp32
    oveq2d
    eqtr3d
    sylan
    breqtrd
    exp32
    rexlimiv
    mpcom
end
