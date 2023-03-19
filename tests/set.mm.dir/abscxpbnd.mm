include "ccxp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cre.mm"
include "cpi.mm"
include "cmul.mm"
include "ce.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "1le1.mm"
include "a1i.mm"
include "oveq12.mm"
include "adantll.mm"
include "cc.mm"
include "wcel.mm"
include "0cn.mm"
include "cxp0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "abs1.mm"
include "fveq2.mm"
include "re0.mm"
include "oveq2d.mm"
include "recnd.mm"
include "cxp0d.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "simpr.mm"
include "abs00bd.mm"
include "oveq1d.mm"
include "picn.mm"
include "mul02i.mm"
include "ef0.mm"
include "oveq12d.mm"
include "1t1e1.mm"
include "3brtr4d.mm"
include "wne.mm"
include "simplr.mm"
include "0cxp.mm"
include "sylan.mm"
include "eqtrd.mm"
include "cr.mm"
include "0red.mm"
include "abscld.mm"
include "absge0d.mm"
include "letrd.mm"
include "recld.mm"
include "recxpcld.mm"
include "ad2antrr.mm"
include "pire.mm"
include "remulcl.mm"
include "sylancl.mm"
include "reefcld.mm"
include "cxpge0d.mm"
include "rpefcld.mm"
include "rpge0d.mm"
include "mulge0d.mm"
include "eqbrtrd.mm"
include "pm2.61dane.mm"
include "cim.mm"
include "clog.mm"
include "cneg.mm"
include "cxpefd.mm"
include "logcl.mm"
include "mulcld.mm"
include "absef.mm"
include "syl.mm"
include "caddc.mm"
include "remulcld.mm"
include "imcld.mm"
include "renegcld.mm"
include "efadd.mm"
include "syl2anc.mm"
include "cmin.mm"
include "negsubd.mm"
include "mulneg2d.mm"
include "remuld.mm"
include "3eqtr4d.mm"
include "relog.mm"
include "abs00ad.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "cxple2ad.mm"
include "lemul1ad.mm"
include "leabsd.mm"
include "absmuld.mm"
include "breqtrd.mm"
include "absimle.mm"
include "absnegd.mm"
include "clt.mm"
include "logimcl.mm"
include "simpld.mm"
include "wi.mm"
include "renegcli.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "simprd.mm"
include "wb.mm"
include "absle.mm"
include "mpbir2and.mm"
include "lemul2ad.mm"
include "efle.mm"
include "mpbid.mm"

theorem abscxpbnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  assume abscxpbnd.1: |- ( ph -> A e. CC )
  assume abscxpbnd.2: |- ( ph -> B e. CC )
  assume abscxpbnd.3: |- ( ph -> 0 <_ ( Re ` B ) )
  assume abscxpbnd.4: |- ( ph -> M e. RR )
  assume abscxpbnd.5: |- ( ph -> ( abs ` A ) <_ M )


  assert |- ( ph -> ( abs ` ( A ^c B ) ) <_ ( ( M ^c ( Re ` B ) ) x. ( exp ` ( ( abs ` B ) x. _pi ) ) ) )

  proof
    wph
    cA
    cB
    ccxp
    co
    #
    cabs
    cfv
    #
    cM
    cB
    cre
    cfv
    #
    ccxp
    co
    #
    cB
    cabs
    cfv
    #
    cpi
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cc0
    wph
    cA
    cc0
    wceq
    #
    wa
    #
    @8
    cB
    cc0
    @10
    cB
    cc0
    wceq
    #
    wa
    #
    c1
    c1
    @1
    @7
    cle
    c1
    c1
    cle
    wbr
    @12
    1le1
    a1i
    @12
    @1
    c1
    cabs
    cfv
    c1
    @12
    @0
    c1
    cabs
    @12
    @0
    cc0
    cc0
    ccxp
    co
    #
    c1
    @9
    @11
    @0
    @13
    wceq
    wph
    cA
    cc0
    cB
    cc0
    ccxp
    oveq12
    adantll
    cc0
    cc
    wcel
    @13
    c1
    wceq
    0cn
    cc0
    cxp0
    ax-mp
    syl6eq
    fveq2d
    abs1
    syl6eq
    @12
    @7
    c1
    c1
    cmul
    co
    c1
    @12
    @3
    c1
    @6
    c1
    cmul
    @11
    @10
    @3
    cM
    cc0
    ccxp
    co
    #
    c1
    @11
    @2
    cc0
    cM
    ccxp
    @11
    @2
    cc0
    cre
    cfv
    cc0
    cB
    cc0
    cre
    fveq2
    re0
    syl6eq
    oveq2d
    wph
    @14
    c1
    wceq
    @9
    wph
    cM
    wph
    cM
    abscxpbnd.4
    recnd
    cxp0d
    adantr
    sylan9eqr
    @12
    @6
    cc0
    ce
    cfv
    c1
    @12
    @5
    cc0
    ce
    @12
    @5
    cc0
    cpi
    cmul
    co
    cc0
    @12
    @4
    cc0
    cpi
    cmul
    @12
    cB
    @10
    @11
    simpr
    abs00bd
    oveq1d
    cpi
    picn
    mul02i
    syl6eq
    fveq2d
    ef0
    syl6eq
    oveq12d
    1t1e1
    syl6eq
    3brtr4d
    @10
    cB
    cc0
    wne
    #
    wa
    #
    @1
    cc0
    @7
    cle
    @16
    @0
    @16
    @0
    cc0
    cB
    ccxp
    co
    #
    cc0
    @16
    cA
    cc0
    cB
    ccxp
    wph
    @9
    @15
    simplr
    oveq1d
    @10
    cB
    cc
    wcel
    #
    @15
    @17
    cc0
    wceq
    wph
    @18
    @9
    abscxpbnd.2
    adantr
    cB
    0cxp
    sylan
    eqtrd
    abs00bd
    @16
    @3
    @6
    wph
    @3
    cr
    wcel
    #
    @9
    @15
    wph
    cM
    @2
    abscxpbnd.4
    wph
    cc0
    cA
    cabs
    cfv
    #
    cM
    wph
    0red
    wph
    cA
    abscxpbnd.1
    abscld
    #
    abscxpbnd.4
    wph
    cA
    abscxpbnd.1
    absge0d
    abscxpbnd.5
    letrd
    #
    wph
    cB
    abscxpbnd.2
    recld
    #
    recxpcld
    #
    ad2antrr
    @16
    @5
    @16
    @4
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    wph
    @25
    @9
    @15
    wph
    cB
    abscxpbnd.2
    abscld
    #
    ad2antrr
    pire
    @4
    cpi
    remulcl
    #
    sylancl
    #
    reefcld
    wph
    cc0
    @3
    cle
    wbr
    #
    @9
    @15
    wph
    cM
    @2
    abscxpbnd.4
    @22
    @23
    cxpge0d
    #
    ad2antrr
    @16
    @6
    @16
    @5
    @30
    rpefcld
    rpge0d
    mulge0d
    eqbrtrd
    pm2.61dane
    wph
    cA
    cc0
    wne
    #
    wa
    #
    @1
    @20
    @2
    ccxp
    co
    #
    cB
    cim
    cfv
    #
    cA
    clog
    cfv
    #
    cim
    cfv
    #
    cneg
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    @7
    cle
    @34
    @1
    cB
    @37
    cmul
    co
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    @43
    cre
    cfv
    #
    ce
    cfv
    #
    @42
    @34
    @0
    @44
    cabs
    @34
    cA
    cB
    wph
    cA
    cc
    wcel
    #
    @33
    abscxpbnd.1
    adantr
    #
    wph
    @33
    simpr
    wph
    @18
    @33
    abscxpbnd.2
    adantr
    #
    cxpefd
    fveq2d
    @34
    @43
    cc
    wcel
    @45
    @47
    wceq
    @34
    cB
    @37
    @50
    wph
    @48
    @33
    @37
    cc
    wcel
    abscxpbnd.1
    cA
    logcl
    sylan
    #
    mulcld
    @43
    absef
    syl
    @34
    @2
    @37
    cre
    cfv
    #
    cmul
    co
    #
    @40
    caddc
    co
    #
    ce
    cfv
    #
    @53
    ce
    cfv
    #
    @41
    cmul
    co
    #
    @47
    @42
    @34
    @53
    cc
    wcel
    @40
    cc
    wcel
    @55
    @57
    wceq
    @34
    @53
    @34
    @2
    @52
    @34
    cB
    @50
    recld
    #
    @34
    @37
    @51
    recld
    remulcld
    recnd
    #
    @34
    @40
    @34
    @36
    @39
    @34
    cB
    @50
    imcld
    #
    @34
    @38
    @34
    @37
    @51
    imcld
    #
    renegcld
    #
    remulcld
    #
    recnd
    @53
    @40
    efadd
    syl2anc
    @34
    @54
    @46
    ce
    @34
    @53
    @36
    @38
    cmul
    co
    #
    cneg
    #
    caddc
    co
    @53
    @64
    cmin
    co
    @54
    @46
    @34
    @53
    @64
    @59
    @34
    @64
    @34
    @36
    @38
    @60
    @61
    remulcld
    recnd
    negsubd
    @34
    @40
    @65
    @53
    caddc
    @34
    @36
    @38
    @34
    @36
    @60
    recnd
    #
    @34
    @38
    @61
    recnd
    #
    mulneg2d
    oveq2d
    @34
    cB
    @37
    @50
    @51
    remuld
    3eqtr4d
    fveq2d
    @34
    @56
    @35
    @41
    cmul
    @34
    @56
    @2
    @20
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    @35
    @34
    @53
    @69
    ce
    @34
    @52
    @68
    @2
    cmul
    wph
    @48
    @33
    @52
    @68
    wceq
    abscxpbnd.1
    cA
    relog
    sylan
    oveq2d
    fveq2d
    @34
    @20
    @2
    wph
    @20
    cc
    wcel
    @33
    wph
    @20
    @21
    recnd
    adantr
    wph
    @20
    cc0
    wne
    @33
    wph
    @20
    cc0
    cA
    cc0
    wph
    cA
    abscxpbnd.1
    abs00ad
    necon3bid
    biimpar
    @34
    @2
    @58
    recnd
    cxpefd
    eqtr4d
    oveq1d
    3eqtr3d
    3eqtrd
    @34
    @42
    @3
    @41
    cmul
    co
    @7
    @34
    @35
    @41
    @34
    @20
    @2
    @34
    cA
    @49
    abscld
    #
    @34
    cA
    @49
    absge0d
    #
    @58
    recxpcld
    #
    @34
    @40
    @63
    reefcld
    #
    remulcld
    @34
    @3
    @41
    wph
    @19
    @33
    @24
    adantr
    #
    @73
    remulcld
    @34
    @3
    @6
    @74
    wph
    @6
    cr
    wcel
    @33
    wph
    @5
    wph
    @25
    @26
    @27
    @28
    pire
    @29
    sylancl
    #
    reefcld
    adantr
    #
    remulcld
    @34
    @35
    @3
    @41
    @72
    @74
    @73
    @34
    @41
    @34
    @40
    @63
    rpefcld
    rpge0d
    @34
    @20
    cM
    @2
    @70
    @71
    wph
    cM
    cr
    wcel
    @33
    abscxpbnd.4
    adantr
    @58
    wph
    cc0
    @2
    cle
    wbr
    @33
    abscxpbnd.3
    adantr
    wph
    @20
    cM
    cle
    wbr
    @33
    abscxpbnd.5
    adantr
    cxple2ad
    lemul1ad
    @34
    @41
    @6
    @3
    @73
    @76
    @74
    wph
    @31
    @33
    @32
    adantr
    @34
    @40
    @5
    cle
    wbr
    #
    @41
    @6
    cle
    wbr
    #
    @34
    @40
    @36
    cabs
    cfv
    #
    @39
    cabs
    cfv
    #
    cmul
    co
    #
    @5
    @63
    @34
    @79
    @80
    @34
    @36
    @66
    abscld
    #
    @34
    @39
    @34
    @39
    @62
    recnd
    #
    abscld
    #
    remulcld
    #
    wph
    @27
    @33
    @75
    adantr
    #
    @34
    @40
    @40
    cabs
    cfv
    @81
    cle
    @34
    @40
    @63
    leabsd
    @34
    @36
    @39
    @66
    @83
    absmuld
    breqtrd
    @34
    @81
    @4
    @80
    cmul
    co
    @5
    @85
    @34
    @4
    @80
    @34
    cB
    @50
    abscld
    #
    @84
    remulcld
    @86
    @34
    @79
    @4
    @80
    @82
    @87
    @84
    @34
    @39
    @83
    absge0d
    @34
    @18
    @79
    @4
    cle
    wbr
    @50
    cB
    absimle
    syl
    lemul1ad
    @34
    @80
    cpi
    @4
    @84
    @26
    @34
    pire
    a1i
    @87
    @34
    cB
    @50
    absge0d
    @34
    @80
    @38
    cabs
    cfv
    #
    cpi
    cle
    @34
    @38
    @67
    absnegd
    @34
    @88
    cpi
    cle
    wbr
    #
    cpi
    cneg
    #
    @38
    cle
    wbr
    #
    @38
    cpi
    cle
    wbr
    #
    @34
    @90
    @38
    clt
    wbr
    #
    @91
    @34
    @93
    @92
    wph
    @48
    @33
    @93
    @92
    wa
    abscxpbnd.1
    cA
    logimcl
    sylan
    #
    simpld
    @34
    @90
    cr
    wcel
    @38
    cr
    wcel
    #
    @93
    @91
    wi
    cpi
    pire
    renegcli
    @61
    @90
    @38
    ltle
    sylancr
    mpd
    @34
    @93
    @92
    @94
    simprd
    @34
    @95
    @26
    @89
    @91
    @92
    wa
    wb
    @61
    pire
    @38
    cpi
    absle
    sylancl
    mpbir2and
    eqbrtrd
    lemul2ad
    letrd
    letrd
    @34
    @40
    cr
    wcel
    @27
    @77
    @78
    wb
    @63
    @86
    @40
    @5
    efle
    syl2anc
    mpbid
    lemul2ad
    letrd
    eqbrtrd
    pm2.61dane
end
