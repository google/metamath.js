include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "ccos.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cpi.mm"
include "cmin.mm"
include "cxr.mm"
include "cr.mm"
include "pire.mm"
include "a1i.mm"
include "resubcld.mm"
include "rexrd.mm"
include "syl5eqel.mm"
include "caddc.mm"
include "readdcld.mm"
include "clt.mm"
include "wbr.mm"
include "pipos.mm"
include "ltsubpos.mm"
include "mpbii.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"
include "ltaddpos.mm"
include "syl6breqr.mm"
include "eliood.mm"
include "wceq.mm"
include "cz.mm"
include "cmul.mm"
include "eldifi.mm"
include "elioored.mm"
include "adantl.mm"
include "recnd.mm"
include "2cnd.mm"
include "cc.mm"
include "picn.mm"
include "2ne0.mm"
include "gt0ne0ii.mm"
include "divdiv1d.mm"
include "wn.mm"
include "c1.mm"
include "cmo.mm"
include "crp.mm"
include "wb.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcld.mm"
include "mod0.mm"
include "mpbid.mm"
include "peano2zm.mm"
include "syl.mm"
include "ad2antrr.mm"
include "zred.mm"
include "adantr.mm"
include "rerpdivcld.mm"
include "rpred.mm"
include "rpne0d.mm"
include "redivcld.mm"
include "dividd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "divsubdird.mm"
include "eqtr4d.mm"
include "mulid2i.mm"
include "eqcomi.mm"
include "1lt2.mm"
include "1re.mm"
include "2re.mm"
include "ltmul1ii.mm"
include "mpbi.mm"
include "eqbrtri.mm"
include "ltsub2dd.mm"
include "ltdiv1dd.mm"
include "eqbrtrd.mm"
include "w3a.mm"
include "elioo2.mm"
include "simp2d.mm"
include "lttrd.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "divcld.mm"
include "1cnd.mm"
include "npcand.mm"
include "breqtrd.mm"
include "btwnnz.mm"
include "syl3anc.mm"
include "cle.mm"
include "eldifsni.mm"
include "necomd.mm"
include "leneltd.mm"
include "stoic1a.mm"
include "ltnled.mm"
include "mpbird.mm"
include "1red.mm"
include "simp3d.mm"
include "oveq1i.mm"
include "divdird.mm"
include "2cn.mm"
include "mulcomi.mm"
include "oveq2i.mm"
include "pm3.2i.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "mp3an.mm"
include "dividi.mm"
include "3eqtr2i.mm"
include "halflt1.mm"
include "ltadd2dd.mm"
include "pm2.61dan.mm"
include "eqneltrd.mm"
include "halfcld.mm"
include "sineq0.mm"
include "mtbird.mm"
include "neqned.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "mulid1d.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "divcan5d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "rehalfcld.mm"
include "ltadd1dd.mm"
include "addassd.mm"
include "2halvesd.mm"
include "coseq0.mm"
include "jca.mm"
include "ralrimiva.mm"

theorem dirkercncflem1
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume dirkercncflem1.a: |- A = ( Y - _pi )
  assume dirkercncflem1.b: |- B = ( Y + _pi )
  assume dirkercncflem1.y: |- ( ph -> Y e. RR )
  assume dirkercncflem1.ymod0: |- ( ph -> ( Y mod ( 2 x. _pi ) ) = 0 )

  disjoint Y y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( Y e. ( A (,) B ) /\ A. y e. ( ( A (,) B ) \ { Y } ) ( ( sin ` ( y / 2 ) ) =/= 0 /\ ( cos ` ( y / 2 ) ) =/= 0 ) ) )

  proof
    wph
    cY
    cA
    cB
    cioo
    co
    #
    wcel
    vy
    cv
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cc0
    wne
    #
    @2
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    vy
    @0
    cY
    csn
    #
    cdif
    #
    wral
    wph
    cA
    cB
    cY
    wph
    cA
    cY
    cpi
    cmin
    co
    #
    cxr
    dirkercncflem1.a
    wph
    @10
    wph
    cY
    cpi
    dirkercncflem1.y
    cpi
    cr
    wcel
    #
    wph
    pire
    a1i
    #
    resubcld
    #
    rexrd
    syl5eqel
    #
    wph
    cB
    cY
    cpi
    caddc
    co
    #
    cxr
    dirkercncflem1.b
    wph
    @15
    wph
    cY
    cpi
    dirkercncflem1.y
    @12
    readdcld
    #
    rexrd
    syl5eqel
    #
    dirkercncflem1.y
    wph
    cA
    @10
    cY
    clt
    dirkercncflem1.a
    wph
    @11
    cY
    cr
    wcel
    #
    @10
    cY
    clt
    wbr
    #
    @12
    dirkercncflem1.y
    @11
    @18
    wa
    #
    cc0
    cpi
    clt
    wbr
    #
    @19
    pipos
    cpi
    cY
    ltsubpos
    mpbii
    syl2anc
    syl5eqbr
    wph
    cY
    @15
    cB
    clt
    wph
    @11
    @18
    cY
    @15
    clt
    wbr
    #
    @12
    dirkercncflem1.y
    @20
    @21
    @22
    pipos
    cpi
    cY
    ltaddpos
    mpbii
    syl2anc
    dirkercncflem1.b
    syl6breqr
    eliood
    wph
    @7
    vy
    @9
    wph
    @1
    @9
    wcel
    #
    wa
    #
    @4
    @6
    @24
    @3
    cc0
    @24
    @3
    cc0
    wceq
    #
    @2
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    @24
    @26
    @1
    c2
    cpi
    cmul
    co
    #
    cdiv
    co
    #
    cz
    @24
    @1
    c2
    cpi
    @24
    @1
    @23
    @1
    cr
    wcel
    #
    wph
    @23
    @1
    cA
    cB
    @1
    @0
    @8
    eldifi
    #
    elioored
    #
    adantl
    #
    recnd
    #
    @24
    2cnd
    cpi
    cc
    wcel
    #
    @24
    picn
    a1i
    c2
    cc0
    wne
    #
    @24
    2ne0
    a1i
    cpi
    cc0
    wne
    #
    @24
    cpi
    pire
    pipos
    gt0ne0ii
    #
    a1i
    divdiv1d
    #
    @24
    @1
    cY
    clt
    wbr
    #
    @29
    cz
    wcel
    wn
    #
    @24
    @40
    wa
    #
    cY
    @28
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @44
    @29
    clt
    wbr
    #
    @29
    @44
    c1
    caddc
    co
    #
    clt
    wbr
    @41
    wph
    @45
    @23
    @40
    wph
    @43
    cz
    wcel
    #
    @45
    wph
    cY
    @28
    cmo
    co
    cc0
    wceq
    #
    @48
    dirkercncflem1.ymod0
    wph
    @18
    @28
    crp
    wcel
    #
    @49
    @48
    wb
    dirkercncflem1.y
    wph
    c2
    cpi
    c2
    crp
    wcel
    wph
    2rp
    a1i
    cpi
    crp
    wcel
    wph
    pirp
    a1i
    rpmulcld
    #
    cY
    @28
    mod0
    syl2anc
    mpbid
    #
    @43
    peano2zm
    syl
    #
    ad2antrr
    @24
    @46
    @40
    @24
    @44
    cA
    @28
    cdiv
    co
    #
    @29
    wph
    @44
    cr
    wcel
    @23
    wph
    @44
    @53
    zred
    adantr
    wph
    @54
    cr
    wcel
    @23
    wph
    cA
    @28
    wph
    cA
    @10
    cr
    dirkercncflem1.a
    @13
    syl5eqel
    #
    @51
    rerpdivcld
    adantr
    #
    @24
    @1
    @28
    @33
    wph
    @28
    cr
    wcel
    @23
    wph
    @28
    @51
    rpred
    #
    adantr
    wph
    @28
    cc0
    wne
    @23
    wph
    @28
    @51
    rpne0d
    #
    adantr
    redivcld
    #
    wph
    @44
    @54
    clt
    wbr
    @23
    wph
    @44
    cY
    @28
    cmin
    co
    #
    @28
    cdiv
    co
    #
    @54
    clt
    wph
    @44
    @43
    @28
    @28
    cdiv
    co
    #
    cmin
    co
    @61
    wph
    c1
    @62
    @43
    cmin
    wph
    @62
    c1
    wph
    @28
    wph
    @28
    @57
    recnd
    #
    @58
    dividd
    eqcomd
    oveq2d
    wph
    cY
    @28
    @28
    wph
    cY
    dirkercncflem1.y
    recnd
    #
    @63
    @63
    @58
    divsubdird
    eqtr4d
    wph
    @60
    cA
    @28
    wph
    cY
    @28
    dirkercncflem1.y
    @57
    resubcld
    @55
    @51
    wph
    @60
    @10
    cA
    clt
    wph
    cpi
    @28
    cY
    @12
    @57
    dirkercncflem1.y
    cpi
    @28
    clt
    wbr
    wph
    cpi
    c1
    cpi
    cmul
    co
    #
    @28
    clt
    @65
    cpi
    cpi
    picn
    mulid2i
    eqcomi
    c1
    c2
    clt
    wbr
    @65
    @28
    clt
    wbr
    1lt2
    c1
    c2
    cpi
    1re
    2re
    pire
    pipos
    ltmul1ii
    mpbi
    eqbrtri
    a1i
    ltsub2dd
    dirkercncflem1.a
    syl6breqr
    ltdiv1dd
    eqbrtrd
    adantr
    @24
    cA
    @1
    @28
    wph
    cA
    cr
    wcel
    @23
    @55
    adantr
    @33
    wph
    @50
    @23
    @51
    adantr
    #
    @24
    @30
    cA
    @1
    clt
    wbr
    #
    @1
    cB
    clt
    wbr
    #
    @24
    @1
    @0
    wcel
    #
    @30
    @67
    @68
    w3a
    #
    @23
    @69
    wph
    @31
    adantl
    @24
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @69
    @70
    wb
    wph
    @71
    @23
    @14
    adantr
    wph
    @72
    @23
    @17
    adantr
    cA
    cB
    @1
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    ltdiv1dd
    #
    lttrd
    adantr
    @42
    @29
    @43
    @47
    clt
    @42
    @1
    cY
    @28
    @23
    @30
    wph
    @40
    @32
    ad2antlr
    wph
    @18
    @23
    @40
    dirkercncflem1.y
    ad2antrr
    wph
    @50
    @23
    @40
    @51
    ad2antrr
    @24
    @40
    simpr
    ltdiv1dd
    @24
    @43
    @47
    wceq
    @40
    @24
    @47
    @43
    @24
    @43
    c1
    wph
    @43
    cc
    wcel
    @23
    wph
    cY
    @28
    @64
    @63
    @58
    divcld
    #
    adantr
    @24
    1cnd
    npcand
    eqcomd
    adantr
    breqtrd
    @44
    @29
    btwnnz
    syl3anc
    @24
    @40
    wn
    #
    wa
    #
    @48
    @43
    @29
    clt
    wbr
    @29
    @43
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @41
    wph
    @48
    @23
    @76
    @52
    ad2antrr
    @77
    cY
    @1
    @28
    wph
    @18
    @23
    @76
    dirkercncflem1.y
    ad2antrr
    #
    @24
    @30
    @76
    @33
    adantr
    #
    @24
    @50
    @76
    @66
    adantr
    @77
    cY
    @1
    clt
    wbr
    @1
    cY
    cle
    wbr
    #
    wn
    @24
    @82
    @40
    @24
    @82
    wa
    @1
    cY
    @24
    @30
    @82
    @33
    adantr
    wph
    @18
    @23
    @82
    dirkercncflem1.y
    ad2antrr
    @24
    @82
    simpr
    @23
    cY
    @1
    wne
    wph
    @82
    @23
    @1
    cY
    @1
    @0
    cY
    eldifsni
    necomd
    ad2antlr
    leneltd
    stoic1a
    @77
    cY
    @1
    @80
    @81
    ltnled
    mpbird
    ltdiv1dd
    @24
    @79
    @76
    @24
    @29
    cB
    @28
    cdiv
    co
    #
    @78
    @59
    wph
    @83
    cr
    wcel
    @23
    wph
    cB
    @28
    wph
    cB
    @15
    cr
    dirkercncflem1.b
    @16
    syl5eqel
    #
    @51
    rerpdivcld
    adantr
    #
    @24
    @43
    c1
    wph
    @43
    cr
    wcel
    @23
    wph
    cY
    @28
    dirkercncflem1.y
    @51
    rerpdivcld
    #
    adantr
    @24
    1red
    #
    readdcld
    @24
    @1
    cB
    @28
    @33
    wph
    cB
    cr
    wcel
    @23
    @84
    adantr
    @66
    @24
    @30
    @67
    @68
    @73
    simp3d
    ltdiv1dd
    #
    wph
    @83
    @78
    clt
    wbr
    @23
    wph
    @83
    @15
    @28
    cdiv
    co
    #
    @78
    clt
    cB
    @15
    @28
    cdiv
    dirkercncflem1.b
    oveq1i
    #
    wph
    @89
    @43
    cpi
    @28
    cdiv
    co
    #
    caddc
    co
    #
    @78
    clt
    wph
    cY
    cpi
    @28
    @64
    @35
    wph
    picn
    a1i
    #
    @63
    @58
    divdird
    #
    wph
    @91
    c1
    @43
    wph
    cpi
    @28
    @12
    @51
    rerpdivcld
    wph
    1red
    @86
    @91
    c1
    clt
    wbr
    wph
    @91
    c1
    c2
    cdiv
    co
    #
    c1
    clt
    @91
    cpi
    cpi
    c2
    cmul
    co
    #
    cdiv
    co
    #
    cpi
    cpi
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    @95
    @28
    @96
    cpi
    cdiv
    c2
    cpi
    2cn
    picn
    mulcomi
    oveq2i
    @35
    @35
    @37
    wa
    c2
    cc
    wcel
    @36
    wa
    @99
    @97
    wceq
    picn
    @35
    @37
    picn
    @38
    pm3.2i
    2cnne0
    cpi
    cpi
    c2
    divdiv1
    mp3an
    @98
    c1
    c2
    cdiv
    cpi
    picn
    @38
    dividi
    oveq1i
    3eqtr2i
    halflt1
    eqbrtri
    a1i
    ltadd2dd
    eqbrtrd
    syl5eqbr
    adantr
    lttrd
    adantr
    @43
    @29
    btwnnz
    syl3anc
    pm2.61dan
    eqneltrd
    @24
    @2
    cc
    wcel
    #
    @25
    @27
    wb
    @24
    @1
    @34
    halfcld
    #
    @2
    sineq0
    syl
    mtbird
    neqned
    @24
    @5
    cc0
    @24
    @5
    cc0
    wceq
    #
    @26
    @95
    caddc
    co
    #
    cz
    wcel
    #
    @24
    @103
    @29
    @95
    caddc
    co
    #
    cz
    @24
    @26
    @29
    @95
    caddc
    @39
    oveq1d
    @24
    @48
    @43
    @105
    clt
    wbr
    @105
    @78
    clt
    wbr
    @105
    cz
    wcel
    wn
    wph
    @48
    @23
    @52
    adantr
    @24
    @43
    @54
    @95
    caddc
    co
    #
    @105
    clt
    wph
    @43
    @106
    wceq
    @23
    wph
    @43
    cA
    cpi
    caddc
    co
    #
    @28
    cdiv
    co
    @54
    @91
    caddc
    co
    @106
    wph
    cY
    @107
    @28
    cdiv
    wph
    @107
    @10
    cpi
    caddc
    co
    cY
    wph
    cA
    @10
    cpi
    caddc
    cA
    @10
    wceq
    wph
    dirkercncflem1.a
    a1i
    oveq1d
    wph
    cY
    cpi
    @64
    @93
    npcand
    eqtr2d
    oveq1d
    wph
    cA
    cpi
    @28
    wph
    cA
    @55
    recnd
    @93
    @63
    @58
    divdird
    wph
    @91
    @95
    @54
    caddc
    wph
    @91
    cpi
    c1
    cmul
    co
    #
    @96
    cdiv
    co
    @95
    wph
    cpi
    @108
    @28
    @96
    cdiv
    wph
    @108
    cpi
    wph
    cpi
    @93
    mulid1d
    eqcomd
    wph
    c2
    cpi
    wph
    2cnd
    #
    @93
    mulcomd
    oveq12d
    wph
    c1
    c2
    cpi
    wph
    1cnd
    #
    @109
    @93
    @36
    wph
    2ne0
    a1i
    @37
    wph
    @38
    a1i
    divcan5d
    eqtrd
    #
    oveq2d
    3eqtrd
    adantr
    @24
    @54
    @29
    @95
    @56
    @59
    @24
    c1
    @87
    rehalfcld
    #
    @74
    ltadd1dd
    eqbrtrd
    @24
    @105
    @83
    @95
    caddc
    co
    #
    @78
    clt
    @24
    @29
    @83
    @95
    @59
    @85
    @112
    @88
    ltadd1dd
    wph
    @113
    @78
    wceq
    @23
    wph
    @113
    @89
    @95
    caddc
    co
    @43
    @95
    caddc
    co
    #
    @95
    caddc
    co
    #
    @78
    wph
    @83
    @89
    @95
    caddc
    @83
    @89
    wceq
    wph
    @90
    a1i
    oveq1d
    wph
    @89
    @114
    @95
    caddc
    wph
    @89
    @92
    @114
    @94
    wph
    @91
    @95
    @43
    caddc
    @111
    oveq2d
    eqtrd
    oveq1d
    wph
    @115
    @43
    @95
    @95
    caddc
    co
    #
    caddc
    co
    @78
    wph
    @43
    @95
    @95
    @75
    wph
    c1
    @110
    halfcld
    #
    @117
    addassd
    wph
    @116
    c1
    @43
    caddc
    wph
    c1
    @110
    2halvesd
    oveq2d
    eqtrd
    3eqtrd
    adantr
    breqtrd
    @43
    @105
    btwnnz
    syl3anc
    eqneltrd
    @24
    @100
    @102
    @104
    wb
    @101
    @2
    coseq0
    syl
    mtbird
    neqned
    jca
    ralrimiva
    jca
end
