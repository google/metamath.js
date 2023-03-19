include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ct0.mm"
include "wel.mm"
include "wb.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "word.mm"
include "eloni.mm"
include "cv.mm"
include "wa.mm"
include "wal.mm"
include "df-ral.mm"
include "ordelon.mm"
include "anim12dan.mm"
include "ordsuc.mm"
include "ex.mm"
include "sylbi.mm"
include "adantr.mm"
include "wn.mm"
include "notbi.mm"
include "wss.mm"
include "ontri1.mm"
include "onsssuc.mm"
include "bitr3d.mm"
include "adantrr.mm"
include "adantrl.mm"
include "bibi12d.mm"
include "ancoms.mm"
include "syl5bb.mm"
include "biimpd.mm"
include "syl6an.mm"
include "a2d.mm"
include "ordelss.mm"
include "ordelord.mm"
include "ordsucsssuc.mm"
include "syldan.mm"
include "mpbid.mm"
include "ssneld.mm"
include "jcad.mm"
include "pm5.21.mm"
include "syl6.mm"
include "idd.mm"
include "jad.mm"
include "syld.mm"
include "alimdv.mm"
include "syl5bi.mm"
include "wceq.mm"
include "dfcleq.mm"
include "suc11.mm"
include "syl5bbr.mm"
include "syl.mm"
include "sylibd.mm"
include "ralrimivva.mm"
include "ctopon.mm"
include "cfv.mm"
include "onsuctopon.mm"
include "ist0-2.mm"
include "mpbird.mm"

theorem onsuct0
  let cA: class A
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> suc A e. Kol2 )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    ct0
    wcel
    #
    vx
    vo
    wel
    #
    vy
    vo
    wel
    #
    wb
    #
    vo
    @1
    wral
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @0
    cA
    word
    #
    @9
    cA
    eloni
    @10
    @8
    vx
    vy
    cA
    cA
    @10
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    wa
    #
    @6
    vo
    cv
    #
    @11
    csuc
    #
    wcel
    #
    @17
    @13
    csuc
    #
    wcel
    #
    wb
    #
    vo
    wal
    #
    @7
    @6
    @17
    @1
    wcel
    #
    @5
    wi
    #
    vo
    wal
    @16
    @23
    @5
    vo
    @1
    df-ral
    @16
    @25
    @22
    vo
    @16
    @25
    @24
    @22
    wi
    @22
    @16
    @24
    @5
    @22
    @16
    @11
    con0
    wcel
    #
    @13
    con0
    wcel
    #
    wa
    #
    @24
    @17
    con0
    wcel
    #
    @5
    @22
    wi
    @10
    @12
    @26
    @14
    @27
    cA
    @11
    ordelon
    cA
    @13
    ordelon
    anim12dan
    #
    @10
    @24
    @29
    wi
    #
    @15
    @10
    @1
    word
    #
    @31
    cA
    ordsuc
    @32
    @24
    @29
    @1
    @17
    ordelon
    ex
    sylbi
    adantr
    @28
    @29
    wa
    #
    @5
    @22
    @5
    @3
    wn
    #
    @4
    wn
    #
    wb
    #
    @33
    @22
    @3
    @4
    notbi
    @29
    @28
    @36
    @22
    wb
    @29
    @28
    wa
    @34
    @19
    @35
    @21
    @29
    @26
    @34
    @19
    wb
    @27
    @29
    @26
    wa
    @17
    @11
    wss
    @34
    @19
    @17
    @11
    ontri1
    @17
    @11
    onsssuc
    bitr3d
    adantrr
    @29
    @27
    @35
    @21
    wb
    @26
    @29
    @27
    wa
    @17
    @13
    wss
    @35
    @21
    @17
    @13
    ontri1
    @17
    @13
    onsssuc
    bitr3d
    adantrl
    bibi12d
    ancoms
    syl5bb
    biimpd
    syl6an
    a2d
    @16
    @24
    @22
    @22
    @16
    @24
    wn
    #
    @19
    wn
    #
    @21
    wn
    #
    wa
    @22
    @16
    @37
    @38
    @39
    @10
    @12
    @37
    @38
    wi
    @14
    @10
    @12
    wa
    #
    @18
    @1
    @17
    @40
    @11
    cA
    wss
    #
    @18
    @1
    wss
    #
    cA
    @11
    ordelss
    @10
    @12
    @11
    word
    #
    @41
    @42
    wb
    #
    cA
    @11
    ordelord
    @43
    @10
    @44
    @11
    cA
    ordsucsssuc
    ancoms
    syldan
    mpbid
    ssneld
    adantrr
    @10
    @14
    @37
    @39
    wi
    @12
    @10
    @14
    wa
    #
    @20
    @1
    @17
    @45
    @13
    cA
    wss
    #
    @20
    @1
    wss
    #
    cA
    @13
    ordelss
    @10
    @14
    @13
    word
    #
    @46
    @47
    wb
    #
    cA
    @13
    ordelord
    @48
    @10
    @49
    @13
    cA
    ordsucsssuc
    ancoms
    syldan
    mpbid
    ssneld
    adantrl
    jcad
    @19
    @21
    pm5.21
    syl6
    @16
    @22
    idd
    jad
    syld
    alimdv
    syl5bi
    @16
    @28
    @23
    @7
    wb
    @30
    @23
    @18
    @20
    wceq
    @28
    @7
    vo
    @18
    @20
    dfcleq
    @11
    @13
    suc11
    syl5bbr
    syl
    sylibd
    ralrimivva
    syl
    @0
    @1
    cA
    ctopon
    cfv
    wcel
    @2
    @9
    wb
    cA
    onsuctopon
    vx
    vy
    vo
    @1
    cA
    ist0-2
    syl
    mpbird
end
