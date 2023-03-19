include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "com.mm"
include "wrex.mm"
include "isfi.mm"
include "wral.mm"
include "con0.mm"
include "nnon.mm"
include "wceq.mm"
include "eleq1.mm"
include "breq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "imbi12d.mm"
include "wpss.mm"
include "rspe.mm"
include "sylibr.mm"
include "19.21v.mm"
include "ralbii.mm"
include "ralcom4.mm"
include "bitr3i.mm"
include "wss.mm"
include "pssss.mm"
include "ssfi.mm"
include "sylib.mm"
include "syl2an.mm"
include "csdm.mm"
include "ensym.mm"
include "ad2antll.mm"
include "php3.mm"
include "sylan.mm"
include "adantr.mm"
include "simpllr.mm"
include "sdomentr.mm"
include "syl2anc.mm"
include "ensdomtr.mm"
include "ad2antrl.mm"
include "ad3antrrr.mm"
include "sdomel.mm"
include "mpd.mm"
include "ex.mm"
include "simpr.mm"
include "a1i.mm"
include "jcad.mm"
include "reximdv2.mm"
include "r19.29.mm"
include "expcom.mm"
include "syl.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "mpan.mm"
include "ad2antrr.mm"
include "sseld.mm"
include "pm2.27.mm"
include "impd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "syld.mm"
include "com23.mm"
include "alimdv.mm"
include "syl5bi.mm"
include "sylsyld.mm"
include "impancom.mm"
include "alrimiv.mm"
include "breq1.mm"
include "cbvalv.mm"
include "syl6ibr.mm"
include "tfis2.mm"
include "mpcom.mm"
include "rgen.mm"
include "sylbi.mm"
include "spcgv.mm"
include "rexlimdvw.mm"

theorem findcard3
  let wph: wff ph
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z
  assume findcard3.1: |- ( x = y -> ( ph <-> ch ) )
  assume findcard3.2: |- ( x = A -> ( ph <-> ta ) )
  assume findcard3.3: |- ( y e. Fin -> ( A. x ( x C. y -> ph ) -> ch ) )

  disjoint x y
  disjoint ph y
  disjoint A x
  disjoint ta x
  disjoint ch x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint ph w
  disjoint ph z
  disjoint A w
  disjoint ta w
  assert |- ( A e. Fin -> ta )

  proof
    cA
    cfn
    wcel
    #
    vx
    cv
    #
    vw
    cv
    #
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    #
    cA
    @2
    cen
    wbr
    #
    wa
    #
    vw
    com
    wrex
    #
    wta
    @0
    @6
    vw
    com
    wrex
    #
    @8
    vw
    cA
    isfi
    @5
    vw
    com
    wral
    @9
    @8
    @5
    vw
    com
    @2
    con0
    wcel
    #
    @2
    com
    wcel
    #
    @5
    @2
    nnon
    #
    @11
    @5
    wi
    #
    vz
    cv
    #
    com
    wcel
    #
    @1
    @14
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    vw
    vz
    @2
    @14
    wceq
    #
    @11
    @15
    @5
    @18
    @2
    @14
    com
    eleq1
    @20
    @4
    @17
    vx
    @20
    @3
    @16
    wph
    @2
    @14
    @1
    cen
    breq2
    imbi1d
    albidv
    imbi12d
    @19
    vz
    @2
    wral
    #
    @13
    wi
    @10
    @21
    @11
    vy
    cv
    #
    @2
    cen
    wbr
    #
    wch
    wi
    #
    vy
    wal
    #
    @5
    @11
    @21
    @25
    @11
    @21
    wa
    @24
    vy
    @11
    @23
    @21
    wch
    @11
    @23
    wa
    #
    @22
    cfn
    wcel
    #
    @21
    @1
    @22
    wpss
    #
    wph
    wi
    #
    vx
    wal
    #
    wch
    @26
    @23
    vw
    com
    wrex
    @27
    @23
    vw
    com
    rspe
    vw
    @22
    isfi
    sylibr
    #
    @21
    @15
    @17
    wi
    #
    vz
    @2
    wral
    #
    vx
    wal
    #
    @26
    @30
    @21
    @32
    vx
    wal
    #
    vz
    @2
    wral
    @34
    @35
    @19
    vz
    @2
    @15
    @17
    vx
    19.21v
    ralbii
    @32
    vz
    vx
    @2
    ralcom4
    bitr3i
    @26
    @33
    @29
    vx
    @26
    @28
    @33
    wph
    @26
    @28
    @33
    wph
    wi
    @26
    @28
    wa
    #
    @33
    @32
    @16
    wa
    #
    vz
    @2
    wrex
    #
    wph
    @36
    @16
    vz
    @2
    wrex
    #
    @33
    @38
    wi
    @36
    @16
    vz
    com
    wrex
    #
    @39
    @26
    @27
    @1
    @22
    wss
    #
    @40
    @28
    @31
    @1
    @22
    pssss
    @27
    @41
    wa
    @1
    cfn
    wcel
    @40
    @22
    @1
    ssfi
    vz
    @1
    isfi
    sylib
    syl2an
    @36
    @16
    @16
    vz
    com
    @2
    @36
    @15
    @16
    wa
    #
    @14
    @2
    wcel
    #
    @16
    @36
    @42
    @43
    @36
    @42
    wa
    #
    @14
    @2
    csdm
    wbr
    #
    @43
    @44
    @14
    @1
    cen
    wbr
    #
    @1
    @2
    csdm
    wbr
    #
    @45
    @16
    @46
    @36
    @15
    @1
    @14
    ensym
    ad2antll
    @44
    @1
    @22
    csdm
    wbr
    #
    @23
    @47
    @36
    @48
    @42
    @26
    @27
    @28
    @48
    @31
    @22
    @1
    php3
    sylan
    adantr
    @11
    @23
    @28
    @42
    simpllr
    @1
    @22
    @2
    sdomentr
    syl2anc
    @14
    @1
    @2
    ensdomtr
    syl2anc
    @44
    @14
    con0
    wcel
    #
    @10
    @45
    @43
    wi
    @15
    @49
    @36
    @16
    @14
    nnon
    ad2antrl
    @11
    @10
    @23
    @28
    @42
    @12
    ad3antrrr
    @14
    @2
    sdomel
    syl2anc
    mpd
    ex
    @42
    @16
    wi
    @36
    @15
    @16
    simpr
    a1i
    jcad
    reximdv2
    mpd
    @33
    @39
    @38
    @32
    @16
    vz
    @2
    r19.29
    expcom
    syl
    @36
    @37
    wph
    vz
    @2
    @36
    @43
    @15
    @37
    wph
    wi
    @36
    @2
    com
    @14
    @11
    @2
    com
    wss
    #
    @23
    @28
    com
    word
    @11
    @50
    ordom
    com
    @2
    ordelss
    mpan
    ad2antrr
    sseld
    @15
    @32
    @16
    wph
    @15
    @17
    pm2.27
    impd
    syl6
    rexlimdv
    syld
    ex
    com23
    alimdv
    syl5bi
    findcard3.3
    sylsyld
    impancom
    alrimiv
    expcom
    @4
    @24
    vx
    vy
    @1
    @22
    wceq
    @3
    @23
    wph
    wch
    @1
    @22
    @2
    cen
    breq1
    findcard3.1
    imbi12d
    cbvalv
    syl6ibr
    a1i
    tfis2
    mpcom
    rgen
    @5
    @6
    vw
    com
    r19.29
    mpan
    sylbi
    @0
    @7
    wta
    vw
    com
    @0
    @5
    @6
    wta
    @4
    @6
    wta
    wi
    vx
    cA
    cfn
    @1
    cA
    wceq
    @3
    @6
    wph
    wta
    @1
    cA
    @2
    cen
    breq1
    findcard3.2
    imbi12d
    spcgv
    impd
    rexlimdvw
    mpd
end
