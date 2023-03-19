include "cz.mm"
include "wcel.mm"
include "cdvds.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "cab.mm"
include "iddvds.mm"
include "breq2.mm"
include "elabg.mm"
include "mpbird.mm"
include "wrel.mm"
include "wceq.mm"
include "reldvds.mm"
include "relimasn.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "ssel.mm"
include "syl5.mm"
include "elab2g.mm"
include "mpbidi.mm"
include "com12.mm"
include "adantr.mm"
include "crab.mm"
include "cc0.mm"
include "ssid.mm"
include "simpl.mm"
include "breq1.mm"
include "dvdszrcl.mm"
include "simprd.mm"
include "0dvds.mm"
include "syl.mm"
include "sylan9bbr.mm"
include "mpbid.mm"
include "breq1d.mm"
include "sylan9bb.mm"
include "rabbidva.mm"
include "0z.mm"
include "rabsn.mm"
include "syl6eq.mm"
include "rabbidv.mm"
include "rabbiia.mm"
include "eqtri.mm"
include "adantl.mm"
include "sseq12d.mm"
include "mpbiri.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "zcnd.mm"
include "ad2antrr.mm"
include "simpld.mm"
include "simplr.mm"
include "divcan2d.mm"
include "w3a.mm"
include "dvdsval2.mm"
include "biimpd.mm"
include "3com23.mm"
include "3expa.mm"
include "sylan.mm"
include "imp.mm"
include "anabss1.mm"
include "jca.mm"
include "muldvds1.mm"
include "sylbird.mm"
include "ss2rabdv.mm"
include "cbvrabv.mm"
include "3sstr3g.mm"
include "pm2.61dane.mm"
include "abbidv.mm"
include "eqeq12d.mm"
include "simpr.mm"
include "ancri.mm"
include "impbii.mm"
include "elrab.mm"
include "vex.mm"
include "elab.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "vtoclg.mm"
include "syl5ib.mm"
include "sseq12i.mm"
include "syl6ibr.mm"
include "impbid.mm"
include "syl2anc.mm"

theorem nzss
  let wph: wff ph
  let cM: class M
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assume nzss.m: |- ( ph -> M e. ZZ )
  assume nzss.n: |- ( ph -> N e. V )


  assert |- ( ph -> ( ( || " { M } ) C_ ( || " { N } ) <-> N || M ) )

  proof
    wph
    cM
    cz
    wcel
    #
    cN
    cV
    wcel
    #
    cdvds
    cM
    csn
    cima
    #
    cdvds
    cN
    csn
    cima
    #
    wss
    #
    cN
    cM
    cdvds
    wbr
    #
    wb
    nzss.m
    nzss.n
    @0
    @1
    wa
    #
    @4
    @5
    @0
    @4
    @5
    wi
    @1
    @4
    @0
    @5
    @0
    cM
    @3
    wcel
    #
    @5
    @4
    @0
    cM
    @2
    wcel
    @4
    @7
    @0
    cM
    cM
    vx
    cv
    #
    cdvds
    wbr
    #
    vx
    cab
    #
    @2
    @0
    cM
    @10
    wcel
    cM
    cM
    cdvds
    wbr
    #
    cM
    iddvds
    @9
    @11
    vx
    cM
    cz
    @8
    cM
    cM
    cdvds
    breq2
    elabg
    mpbird
    cdvds
    wrel
    #
    @2
    @10
    wceq
    reldvds
    vx
    cM
    cdvds
    relimasn
    ax-mp
    #
    syl6eleqr
    @2
    @3
    cM
    ssel
    syl5
    cN
    @8
    cdvds
    wbr
    #
    @5
    vx
    cM
    @3
    cz
    @8
    cM
    cN
    cdvds
    breq2
    @12
    @3
    @14
    vx
    cab
    #
    wceq
    reldvds
    vx
    cN
    cdvds
    relimasn
    ax-mp
    #
    elab2g
    mpbidi
    com12
    adantr
    @6
    @5
    @10
    @15
    wss
    #
    @4
    @5
    @9
    vx
    cz
    crab
    #
    @14
    vx
    cz
    crab
    #
    wss
    #
    @6
    @17
    @5
    @20
    cN
    cc0
    @5
    cN
    cc0
    wceq
    #
    wa
    #
    @20
    cc0
    csn
    #
    @23
    wss
    @23
    ssid
    @22
    @18
    @23
    @19
    @23
    @22
    @18
    @8
    cc0
    wceq
    #
    vx
    cz
    crab
    #
    @23
    @22
    @9
    @24
    vx
    cz
    @22
    @9
    cc0
    @8
    cdvds
    wbr
    #
    @8
    cz
    wcel
    @24
    @22
    cM
    cc0
    @8
    cdvds
    @22
    @5
    cM
    cc0
    wceq
    #
    @5
    @21
    simpl
    @21
    @5
    cc0
    cM
    cdvds
    wbr
    #
    @5
    @27
    cN
    cc0
    cM
    cdvds
    breq1
    @5
    @0
    @28
    @27
    wb
    @5
    cN
    cz
    wcel
    #
    @0
    cN
    cM
    dvdszrcl
    #
    simprd
    #
    cM
    0dvds
    syl
    sylan9bbr
    mpbid
    breq1d
    @8
    0dvds
    #
    sylan9bb
    rabbidva
    cc0
    cz
    wcel
    @25
    @23
    wceq
    0z
    vx
    cz
    cc0
    rabsn
    ax-mp
    #
    syl6eq
    @21
    @19
    @23
    wceq
    @5
    @21
    @19
    @26
    vx
    cz
    crab
    #
    @23
    @21
    @14
    @26
    vx
    cz
    cN
    cc0
    @8
    cdvds
    breq1
    rabbidv
    @34
    @25
    @23
    @26
    @24
    vx
    cz
    @32
    rabbiia
    @33
    eqtri
    syl6eq
    adantl
    sseq12d
    mpbiri
    @5
    cN
    cc0
    wne
    #
    wa
    #
    cM
    vn
    cv
    #
    cdvds
    wbr
    #
    vn
    cz
    crab
    cN
    @37
    cdvds
    wbr
    #
    vn
    cz
    crab
    @18
    @19
    @36
    @38
    @39
    vn
    cz
    @36
    @37
    cz
    wcel
    #
    wa
    #
    @38
    cN
    cM
    cN
    cdiv
    co
    #
    cmul
    co
    #
    @37
    cdvds
    wbr
    #
    @39
    @41
    @43
    cM
    @37
    cdvds
    @41
    cM
    cN
    @5
    cM
    cc
    wcel
    @35
    @40
    @5
    cM
    @31
    zcnd
    ad2antrr
    @5
    cN
    cc
    wcel
    @35
    @40
    @5
    cN
    @5
    @29
    @0
    @30
    simpld
    #
    zcnd
    ad2antrr
    @5
    @35
    @40
    simplr
    divcan2d
    breq1d
    @36
    @29
    @42
    cz
    wcel
    #
    wa
    @40
    @44
    @39
    wi
    #
    @36
    @29
    @46
    @5
    @29
    @35
    @45
    adantr
    @5
    @35
    @46
    @36
    @5
    @46
    @5
    @29
    @0
    wa
    @35
    @5
    @46
    wi
    #
    @30
    @29
    @0
    @35
    @48
    @29
    @35
    @0
    @48
    @29
    @35
    @0
    w3a
    @5
    @46
    cN
    cM
    dvdsval2
    biimpd
    3com23
    3expa
    sylan
    imp
    anabss1
    jca
    @29
    @46
    @40
    @47
    cN
    @42
    @37
    muldvds1
    3expa
    sylan
    sylbird
    ss2rabdv
    @38
    @9
    vn
    vx
    cz
    @37
    @8
    cM
    cdvds
    breq2
    cbvrabv
    @39
    @14
    vn
    vx
    cz
    @37
    @8
    cN
    cdvds
    breq2
    cbvrabv
    3sstr3g
    pm2.61dane
    @6
    @18
    @10
    @19
    @15
    @0
    @18
    @10
    wceq
    #
    @1
    @37
    @8
    cdvds
    wbr
    #
    vx
    cz
    crab
    #
    @50
    vx
    cab
    #
    wceq
    #
    @49
    vn
    cM
    cz
    @37
    cM
    wceq
    #
    @51
    @18
    @52
    @10
    @54
    @50
    @9
    vx
    cz
    @37
    cM
    @8
    cdvds
    breq1
    #
    rabbidv
    @54
    @50
    @9
    vx
    @55
    abbidv
    eqeq12d
    vy
    @51
    @52
    vy
    cv
    #
    cz
    wcel
    #
    @37
    @56
    cdvds
    wbr
    #
    wa
    #
    @58
    @56
    @51
    wcel
    @56
    @52
    wcel
    @59
    @58
    @57
    @58
    simpr
    @58
    @57
    @58
    @40
    @57
    @37
    @56
    dvdszrcl
    simprd
    ancri
    impbii
    @50
    @58
    vx
    @56
    cz
    @8
    @56
    @37
    cdvds
    breq2
    #
    elrab
    @50
    @58
    vx
    @56
    vy
    vex
    @60
    elab
    3bitr4i
    eqriv
    #
    vtoclg
    adantr
    @1
    @19
    @15
    wceq
    #
    @0
    @53
    @62
    vn
    cN
    cV
    @37
    cN
    wceq
    #
    @51
    @19
    @52
    @15
    @63
    @50
    @14
    vx
    cz
    @37
    cN
    @8
    cdvds
    breq1
    #
    rabbidv
    @63
    @50
    @14
    vx
    @64
    abbidv
    eqeq12d
    @61
    vtoclg
    adantl
    sseq12d
    syl5ib
    @2
    @10
    @3
    @15
    @13
    @16
    sseq12i
    syl6ibr
    impbid
    syl2anc
end
