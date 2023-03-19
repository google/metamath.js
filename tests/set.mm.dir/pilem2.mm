include "cpi.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "crp.mm"
include "csin.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "df-pi.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "inss1.mm"
include "rpssre.mm"
include "sstri.mm"
include "a1i.mm"
include "0re.mm"
include "sseli.mm"
include "rpge0d.mm"
include "rgen.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "cfv.mm"
include "2re.mm"
include "rpred.mm"
include "remulcl.mm"
include "sylancr.mm"
include "c4.mm"
include "cioo.mm"
include "elioore.mm"
include "syl.mm"
include "resubcld.mm"
include "4re.mm"
include "wa.mm"
include "eliooord.mm"
include "simprd.mm"
include "2t2e4.mm"
include "c0.mm"
include "wne.mm"
include "0red.mm"
include "2pos.mm"
include "simpld.mm"
include "lttrd.mm"
include "elrpd.mm"
include "pilem1.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "infrecl.mm"
include "mp3an13.mm"
include "wn.mm"
include "wo.mm"
include "rpre.mm"
include "adantl.mm"
include "letric.mm"
include "ord.mm"
include "cioc.mm"
include "ad2antlr.mm"
include "rpgt0.mm"
include "simpr.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "elioc2.mm"
include "syl3anbrc.mm"
include "sin02gt0.mm"
include "gt0ne0d.mm"
include "ex.mm"
include "syld.mm"
include "necon4bd.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "infrelb.mm"
include "syl3anc.mm"
include "letrd.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "posdifd.mm"
include "ccos.mm"
include "cc.mm"
include "recnd.mm"
include "sinsub.mm"
include "syl2anc.mm"
include "sin2t.mm"
include "oveq1d.mm"
include "coscld.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "2t0e0.mm"
include "syl6eq.mm"
include "mul01d.mm"
include "oveq12d.mm"
include "0m0e0.mm"
include "syl5eqbr.mm"
include "syl5eqel.mm"
include "leaddsub.mm"
include "readdcld.mm"
include "ledivmul.mm"

theorem pilem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume pilem.1: |- ( ph -> A e. ( 2 (,) 4 ) )
  assume pilem.2: |- ( ph -> B e. RR+ )
  assume pilem.3: |- ( ph -> ( sin ` A ) = 0 )
  assume pilem.4: |- ( ph -> ( sin ` B ) = 0 )
  assume pilem.5: |- ( ph -> _pi < A )


  assert |- ( ph -> ( ( _pi + A ) / 2 ) <_ B )

  proof
    wph
    cpi
    cA
    caddc
    co
    #
    c2
    cdiv
    co
    cB
    cle
    wbr
    #
    @0
    c2
    cB
    cmul
    co
    #
    cle
    wbr
    #
    wph
    @3
    cpi
    @2
    cA
    cmin
    co
    #
    cle
    wbr
    #
    wph
    cpi
    crp
    csin
    ccnv
    cc0
    csn
    cima
    #
    cin
    #
    cr
    clt
    cinf
    #
    @4
    cle
    df-pi
    wph
    @7
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @7
    wral
    #
    vx
    cr
    wrex
    #
    @4
    @7
    wcel
    #
    @8
    @4
    cle
    wbr
    @9
    wph
    @7
    crp
    cr
    crp
    @6
    inss1
    #
    rpssre
    sstri
    #
    a1i
    #
    @14
    wph
    cc0
    cr
    wcel
    cc0
    @11
    cle
    wbr
    #
    vy
    @7
    wral
    #
    @14
    0re
    @19
    vy
    @7
    @11
    @7
    wcel
    @11
    @7
    crp
    @11
    @16
    sseli
    rpge0d
    rgen
    @13
    @20
    vx
    cc0
    cr
    @10
    cc0
    wceq
    @12
    @19
    vy
    @7
    @10
    cc0
    @11
    cle
    breq1
    ralbidv
    rspcev
    mp2an
    #
    a1i
    #
    wph
    @4
    crp
    wcel
    @4
    csin
    cfv
    #
    cc0
    wceq
    @15
    wph
    @4
    wph
    @2
    cA
    wph
    c2
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    2re
    wph
    cB
    pilem.2
    rpred
    #
    c2
    cB
    remulcl
    sylancr
    #
    wph
    cA
    c2
    c4
    cioo
    co
    wcel
    #
    cA
    cr
    wcel
    #
    pilem.1
    cA
    c2
    c4
    elioore
    syl
    #
    resubcld
    wph
    cA
    @2
    clt
    wbr
    cc0
    @4
    clt
    wbr
    wph
    cA
    c4
    @2
    @31
    c4
    cr
    wcel
    wph
    4re
    a1i
    @28
    wph
    c2
    cA
    clt
    wbr
    #
    cA
    c4
    clt
    wbr
    #
    wph
    @29
    @32
    @33
    wa
    pilem.1
    cA
    c2
    c4
    eliooord
    syl
    #
    simprd
    wph
    c4
    c2
    c2
    cmul
    co
    #
    @2
    cle
    2t2e4
    wph
    c2
    cB
    cle
    wbr
    #
    @35
    @2
    cle
    wbr
    #
    wph
    c2
    @8
    cB
    @24
    wph
    2re
    a1i
    #
    wph
    @7
    c0
    wne
    #
    @8
    cr
    wcel
    #
    wph
    cA
    @7
    wcel
    #
    @39
    wph
    cA
    crp
    wcel
    cA
    csin
    cfv
    #
    cc0
    wceq
    @41
    wph
    cA
    @31
    wph
    cc0
    c2
    cA
    wph
    0red
    @38
    @31
    cc0
    c2
    clt
    wbr
    #
    wph
    2pos
    a1i
    wph
    @32
    @33
    @34
    simpld
    lttrd
    elrpd
    pilem.3
    cA
    pilem1
    sylanbrc
    @7
    cA
    ne0i
    syl
    #
    @9
    @39
    @14
    @40
    @17
    @21
    vx
    vy
    @7
    infrecl
    mp3an13
    syl
    #
    @27
    wph
    c2
    @8
    cle
    wbr
    #
    c2
    @10
    cle
    wbr
    #
    vx
    @7
    wral
    #
    wph
    @47
    vx
    @7
    @10
    @7
    wcel
    @10
    crp
    wcel
    #
    @10
    csin
    cfv
    #
    cc0
    wceq
    #
    wa
    wph
    @47
    @10
    pilem1
    wph
    @49
    @51
    @47
    wph
    @49
    wa
    #
    @47
    @50
    cc0
    @52
    @47
    wn
    @10
    c2
    cle
    wbr
    #
    @50
    cc0
    wne
    #
    @52
    @47
    @53
    @52
    @24
    @10
    cr
    wcel
    #
    @47
    @53
    wo
    2re
    @49
    @55
    wph
    @10
    rpre
    #
    adantl
    c2
    @10
    letric
    sylancr
    ord
    @52
    @53
    @54
    @52
    @53
    wa
    #
    @50
    @57
    @10
    cc0
    c2
    cioc
    co
    wcel
    #
    cc0
    @50
    clt
    wbr
    @57
    @55
    cc0
    @10
    clt
    wbr
    #
    @53
    @58
    @49
    @55
    wph
    @53
    @56
    ad2antlr
    @49
    @59
    wph
    @53
    @10
    rpgt0
    ad2antlr
    @52
    @53
    simpr
    cc0
    cxr
    wcel
    @24
    @58
    @55
    @59
    @53
    w3a
    wb
    0xr
    2re
    cc0
    c2
    @10
    elioc2
    mp2an
    syl3anbrc
    @10
    sin02gt0
    syl
    gt0ne0d
    ex
    syld
    necon4bd
    expimpd
    syl5bi
    ralrimiv
    wph
    @9
    @39
    @14
    @24
    @46
    @48
    wb
    @18
    @44
    @22
    @38
    vx
    vy
    vx
    @7
    c2
    infregelb
    syl31anc
    mpbird
    wph
    @9
    @14
    cB
    @7
    wcel
    #
    @8
    cB
    cle
    wbr
    @18
    @22
    wph
    cB
    crp
    wcel
    cB
    csin
    cfv
    #
    cc0
    wceq
    @60
    pilem.2
    pilem.4
    cB
    pilem1
    sylanbrc
    vx
    vy
    cB
    @7
    infrelb
    syl3anc
    letrd
    wph
    @24
    @25
    @24
    @43
    wa
    #
    @36
    @37
    wb
    @38
    @27
    @62
    wph
    @24
    @43
    2re
    2pos
    pm3.2i
    a1i
    #
    c2
    cB
    c2
    lemul2
    syl3anc
    mpbid
    syl5eqbrr
    ltletrd
    wph
    cA
    @2
    @31
    @28
    posdifd
    mpbid
    elrpd
    wph
    @23
    @2
    csin
    cfv
    #
    cA
    ccos
    cfv
    #
    cmul
    co
    #
    @2
    ccos
    cfv
    #
    @42
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wph
    @2
    cc
    wcel
    cA
    cc
    wcel
    @23
    @69
    wceq
    wph
    @2
    @28
    recnd
    #
    wph
    cA
    @31
    recnd
    #
    @2
    cA
    sinsub
    syl2anc
    wph
    @69
    cc0
    cc0
    cmin
    co
    cc0
    wph
    @66
    cc0
    @68
    cc0
    cmin
    wph
    @66
    cc0
    @65
    cmul
    co
    cc0
    wph
    @64
    cc0
    @65
    cmul
    wph
    @64
    c2
    @61
    cB
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cc0
    wph
    cB
    cc
    wcel
    @64
    @74
    wceq
    wph
    cB
    @27
    recnd
    #
    cB
    sin2t
    syl
    wph
    @74
    c2
    cc0
    cmul
    co
    cc0
    wph
    @73
    cc0
    c2
    cmul
    wph
    @73
    cc0
    @72
    cmul
    co
    cc0
    wph
    @61
    cc0
    @72
    cmul
    pilem.4
    oveq1d
    wph
    @72
    wph
    cB
    @75
    coscld
    mul02d
    eqtrd
    oveq2d
    2t0e0
    syl6eq
    eqtrd
    oveq1d
    wph
    @65
    wph
    cA
    @71
    coscld
    mul02d
    eqtrd
    wph
    @68
    @67
    cc0
    cmul
    co
    cc0
    wph
    @42
    cc0
    @67
    cmul
    pilem.3
    oveq2d
    wph
    @67
    wph
    @2
    @70
    coscld
    mul01d
    eqtrd
    oveq12d
    0m0e0
    syl6eq
    eqtrd
    @4
    pilem1
    sylanbrc
    vx
    vy
    @4
    @7
    infrelb
    syl3anc
    syl5eqbr
    wph
    cpi
    cr
    wcel
    @30
    @26
    @3
    @5
    wb
    wph
    cpi
    @8
    cr
    df-pi
    @45
    syl5eqel
    #
    @31
    @28
    cpi
    cA
    @2
    leaddsub
    syl3anc
    mpbird
    wph
    @0
    cr
    wcel
    @25
    @62
    @1
    @3
    wb
    wph
    cpi
    cA
    @76
    @31
    readdcld
    @27
    @63
    @0
    cB
    c2
    ledivmul
    syl3anc
    mpbird
end
