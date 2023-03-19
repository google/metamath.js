include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "cii.mm"
include "ccn.mm"
include "wcel.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "cphtpc.mm"
include "wbr.mm"
include "w3a.mm"
include "isphtpc.mm"
include "sylib.mm"
include "simp1d.mm"
include "pcocn.mm"
include "simp2d.mm"
include "c1.mm"
include "cc0.mm"
include "wceq.mm"
include "phtpy01.mm"
include "simprd.mm"
include "simpld.mm"
include "3eqtr3d.mm"
include "cicc.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "eqid.mm"
include "dfii2.mm"
include "0red.mm"
include "1red.mm"
include "cr.mm"
include "halfre.mm"
include "0re.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "1re.mm"
include "halflt1.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "a1i.mm"
include "ctopon.mm"
include "iitopon.mm"
include "wa.mm"
include "adantr.mm"
include "phtpyi.mm"
include "adantrl.mm"
include "3eqtr4d.mm"
include "simprl.mm"
include "oveq2d.mm"
include "2cn.mm"
include "2ne0.mm"
include "recidi.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "1m1e0.mm"
include "wss.mm"
include "retopon.mm"
include "iccssre.mm"
include "mp2an.mm"
include "resttopon.mm"
include "cnmpt1st.mm"
include "cmpt.mm"
include "iihalf1cn.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "cnmpt2nd.mm"
include "phtpycn.mm"
include "sseldd.mm"
include "cnmpt22f.mm"
include "iihalf2cn.mm"
include "weq.mm"
include "cnmpt2pc.mm"
include "syl5eqel.mm"
include "simpll.mm"
include "elii1.mm"
include "iihalf1.mm"
include "sylbir.mm"
include "adantll.mm"
include "chtpy.mm"
include "phtpyhtpy.mm"
include "htpyi.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "elii2.mm"
include "iihalf2.mm"
include "syl.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "simpr.mm"
include "0elunit.mm"
include "simpl.mm"
include "breq1d.mm"
include "oveq12d.mm"
include "ifbieq12d.mm"
include "ovex.mm"
include "ifex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "pcovalg.mm"
include "1elunit.mm"
include "syl6eqbr.mm"
include "iftrued.mm"
include "2t0e0.mm"
include "eqtrd.mm"
include "sylancr.mm"
include "pco0.mm"
include "clt.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "2t1e2.mm"
include "2m1e1.mm"
include "pco1.mm"
include "isphtpy2d.mm"

theorem pcohtpylem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  assume pcohtpy.4: |- ( ph -> ( F ` 1 ) = ( G ` 0 ) )
  assume pcohtpy.5: |- ( ph -> F ( ~=ph ` J ) H )
  assume pcohtpy.6: |- ( ph -> G ( ~=ph ` J ) K )
  assume pcohtpylem.7: |- P = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> if ( x <_ ( 1 / 2 ) , ( ( 2 x. x ) M y ) , ( ( ( 2 x. x ) - 1 ) N y ) ) )
  assume pcohtpylem.8: |- ( ph -> M e. ( F ( PHtpy ` J ) H ) )
  assume pcohtpylem.9: |- ( ph -> N e. ( G ( PHtpy ` J ) K ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint M s
  disjoint N s
  disjoint m z
  disjoint m ph
  disjoint n z
  disjoint n ph
  disjoint s z
  disjoint ph s
  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint G m
  disjoint G n
  disjoint G s
  disjoint H m
  disjoint H n
  disjoint H s
  disjoint J m
  disjoint J n
  disjoint J s
  disjoint P s
  disjoint K m
  disjoint K n
  disjoint K s
  assert |- ( ph -> P e. ( ( F ( *p ` J ) G ) ( PHtpy ` J ) ( H ( *p ` J ) K ) ) )

  proof
    wph
    cF
    cG
    cJ
    cpco
    cfv
    #
    co
    #
    cH
    cK
    @0
    co
    #
    cP
    cJ
    vs
    wph
    cF
    cG
    cJ
    wph
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cH
    @3
    wcel
    #
    cF
    cH
    cJ
    cphtpy
    cfv
    #
    co
    #
    c0
    wne
    #
    wph
    cF
    cH
    cJ
    cphtpc
    cfv
    #
    wbr
    @4
    @5
    @8
    w3a
    pcohtpy.5
    cF
    cH
    cJ
    isphtpc
    sylib
    #
    simp1d
    #
    wph
    cG
    @3
    wcel
    #
    cK
    @3
    wcel
    #
    cG
    cK
    @6
    co
    #
    c0
    wne
    #
    wph
    cG
    cK
    @9
    wbr
    @12
    @13
    @15
    w3a
    pcohtpy.6
    cG
    cK
    cJ
    isphtpc
    sylib
    #
    simp1d
    #
    pcohtpy.4
    pcocn
    wph
    cH
    cK
    cJ
    wph
    @4
    @5
    @8
    @10
    simp2d
    #
    wph
    @12
    @13
    @15
    @16
    simp2d
    #
    wph
    c1
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    c1
    cH
    cfv
    #
    cc0
    cK
    cfv
    #
    pcohtpy.4
    wph
    cc0
    cF
    cfv
    #
    cc0
    cH
    cfv
    wceq
    @20
    @22
    wceq
    wph
    cF
    cH
    cM
    cJ
    @11
    @18
    pcohtpylem.8
    phtpy01
    simprd
    wph
    @21
    @23
    wceq
    c1
    cG
    cfv
    #
    c1
    cK
    cfv
    wceq
    wph
    cG
    cK
    cN
    cJ
    @17
    @19
    pcohtpylem.9
    phtpy01
    simpld
    3eqtr3d
    pcocn
    wph
    cP
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    @26
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    c2
    @27
    cmul
    co
    #
    vy
    cv
    #
    cM
    co
    #
    @30
    c1
    cmin
    co
    #
    @31
    cN
    co
    #
    cif
    #
    cmpt2
    cii
    cii
    ctx
    co
    cJ
    ccn
    co
    #
    pcohtpylem.7
    wph
    vx
    vy
    cc0
    @28
    c1
    @32
    cioo
    crn
    ctg
    cfv
    #
    @34
    cii
    cJ
    @37
    cc0
    @28
    cicc
    co
    #
    crest
    co
    #
    @37
    @28
    c1
    cicc
    co
    #
    crest
    co
    #
    cii
    @26
    @37
    eqid
    @39
    eqid
    #
    @41
    eqid
    #
    dfii2
    wph
    0red
    wph
    1red
    @28
    @26
    wcel
    #
    wph
    @44
    @28
    cr
    wcel
    #
    cc0
    @28
    cle
    wbr
    @28
    c1
    cle
    wbr
    halfre
    cc0
    @28
    0re
    halfre
    halfgt0
    ltleii
    #
    @28
    c1
    halfre
    1re
    halflt1
    ltleii
    cc0
    c1
    @28
    0re
    1re
    elicc2i
    mpbir3an
    a1i
    cii
    @26
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    wph
    @27
    @28
    wceq
    #
    @31
    @26
    wcel
    #
    wa
    #
    wa
    #
    c1
    @31
    cM
    co
    #
    cc0
    @31
    cN
    co
    #
    @32
    @34
    @51
    @20
    @21
    @52
    @53
    wph
    @20
    @21
    wceq
    @50
    pcohtpy.4
    adantr
    wph
    @49
    @52
    @20
    wceq
    #
    @48
    wph
    @49
    wa
    #
    cc0
    @31
    cM
    co
    @24
    wceq
    @54
    wph
    @31
    cF
    cH
    cM
    cJ
    @11
    @18
    pcohtpylem.8
    phtpyi
    simprd
    adantrl
    wph
    @49
    @53
    @21
    wceq
    #
    @48
    @55
    @56
    c1
    @31
    cN
    co
    @25
    wceq
    wph
    @31
    cG
    cK
    cN
    cJ
    @17
    @19
    pcohtpylem.9
    phtpyi
    simpld
    adantrl
    3eqtr4d
    @51
    @30
    c1
    @31
    cM
    @51
    @30
    c2
    @28
    cmul
    co
    c1
    @51
    @27
    @28
    c2
    cmul
    wph
    @48
    @49
    simprl
    oveq2d
    c2
    2cn
    2ne0
    recidi
    syl6eq
    #
    oveq1d
    @51
    @33
    cc0
    @31
    cN
    @51
    @33
    c1
    c1
    cmin
    co
    cc0
    @51
    @30
    c1
    c1
    cmin
    @57
    oveq1d
    1m1e0
    syl6eq
    oveq1d
    3eqtr4d
    wph
    vx
    vy
    @30
    @31
    cM
    @39
    cii
    cii
    cii
    cJ
    @38
    @26
    @39
    @38
    ctopon
    cfv
    wcel
    #
    wph
    @37
    cr
    ctopon
    cfv
    wcel
    #
    @38
    cr
    wss
    #
    @58
    retopon
    cc0
    cr
    wcel
    @45
    @60
    0re
    halfre
    cc0
    @28
    iccssre
    mp2an
    @38
    @37
    cr
    resttopon
    mp2an
    a1i
    #
    @47
    wph
    vx
    vy
    vz
    @27
    c2
    vz
    cv
    #
    cmul
    co
    #
    @30
    @39
    cii
    @39
    cii
    @38
    @26
    @38
    @61
    @47
    wph
    vx
    vy
    @39
    cii
    @38
    @26
    @61
    @47
    cnmpt1st
    @61
    vz
    @38
    @63
    cmpt
    @39
    cii
    ccn
    co
    wcel
    wph
    vz
    @39
    @42
    iihalf1cn
    a1i
    @62
    @27
    c2
    cmul
    oveq2
    #
    cnmpt21
    wph
    vx
    vy
    @39
    cii
    @38
    @26
    @61
    @47
    cnmpt2nd
    wph
    @7
    @36
    cM
    wph
    cF
    cH
    cJ
    @11
    @18
    phtpycn
    pcohtpylem.8
    sseldd
    cnmpt22f
    wph
    vx
    vy
    @33
    @31
    cN
    @41
    cii
    cii
    cii
    cJ
    @40
    @26
    @41
    @40
    ctopon
    cfv
    wcel
    #
    wph
    @59
    @40
    cr
    wss
    #
    @65
    retopon
    @45
    c1
    cr
    wcel
    @66
    halfre
    1re
    @28
    c1
    iccssre
    mp2an
    @40
    @37
    cr
    resttopon
    mp2an
    a1i
    #
    @47
    wph
    vx
    vy
    vz
    @27
    @63
    c1
    cmin
    co
    #
    @33
    @41
    cii
    @41
    cii
    @40
    @26
    @40
    @67
    @47
    wph
    vx
    vy
    @41
    cii
    @40
    @26
    @67
    @47
    cnmpt1st
    @67
    vz
    @40
    @68
    cmpt
    @41
    cii
    ccn
    co
    wcel
    wph
    vz
    @41
    @43
    iihalf2cn
    a1i
    vz
    vx
    weq
    @63
    @30
    c1
    cmin
    @64
    oveq1d
    cnmpt21
    wph
    vx
    vy
    @41
    cii
    @40
    @26
    @67
    @47
    cnmpt2nd
    wph
    @14
    @36
    cN
    wph
    cG
    cK
    cJ
    @17
    @19
    phtpycn
    pcohtpylem.9
    sseldd
    cnmpt22f
    cnmpt2pc
    syl5eqel
    wph
    vs
    cv
    #
    @26
    wcel
    #
    wa
    #
    @69
    @28
    cle
    wbr
    #
    c2
    @69
    cmul
    co
    #
    cc0
    cM
    co
    #
    @73
    c1
    cmin
    co
    #
    cc0
    cN
    co
    #
    cif
    #
    @72
    @73
    cF
    cfv
    #
    @75
    cG
    cfv
    #
    cif
    #
    @69
    cc0
    cP
    co
    #
    @69
    @1
    cfv
    @71
    @72
    @77
    @80
    wceq
    @71
    @72
    wa
    #
    @74
    @78
    @77
    @80
    @82
    @74
    @78
    wceq
    #
    @73
    c1
    cM
    co
    #
    @73
    cH
    cfv
    #
    wceq
    #
    @82
    wph
    @73
    @26
    wcel
    #
    @83
    @86
    wa
    wph
    @70
    @72
    simpll
    @70
    @72
    @87
    wph
    @70
    @72
    wa
    @69
    @38
    wcel
    @87
    @69
    elii1
    @69
    iihalf1
    sylbir
    adantll
    wph
    @73
    cF
    cH
    cM
    cii
    cJ
    @26
    @47
    @11
    @18
    wph
    @7
    cF
    cH
    cii
    cJ
    chtpy
    co
    #
    co
    cM
    wph
    cF
    cH
    cJ
    @11
    @18
    phtpyhtpy
    pcohtpylem.8
    sseldd
    htpyi
    syl2anc
    #
    simpld
    @72
    @77
    @74
    wceq
    @71
    @72
    @74
    @76
    iftrue
    adantl
    @72
    @80
    @78
    wceq
    @71
    @72
    @78
    @79
    iftrue
    adantl
    3eqtr4d
    @71
    @72
    wn
    #
    wa
    #
    @76
    @79
    @77
    @80
    @91
    @76
    @79
    wceq
    #
    @75
    c1
    cN
    co
    #
    @75
    cK
    cfv
    #
    wceq
    #
    @91
    wph
    @75
    @26
    wcel
    #
    @92
    @95
    wa
    wph
    @70
    @90
    simpll
    @91
    @69
    @40
    wcel
    #
    @96
    @70
    @90
    @97
    wph
    @69
    elii2
    adantll
    @69
    iihalf2
    syl
    wph
    @75
    cG
    cK
    cN
    cii
    cJ
    @26
    @47
    @17
    @19
    wph
    @14
    cG
    cK
    @88
    co
    cN
    wph
    cG
    cK
    cJ
    @17
    @19
    phtpyhtpy
    pcohtpylem.9
    sseldd
    htpyi
    syl2anc
    #
    simpld
    @90
    @77
    @76
    wceq
    @71
    @72
    @74
    @76
    iffalse
    adantl
    @90
    @80
    @79
    wceq
    @71
    @72
    @78
    @79
    iffalse
    adantl
    3eqtr4d
    pm2.61dan
    @71
    @70
    cc0
    @26
    wcel
    #
    @81
    @77
    wceq
    wph
    @70
    simpr
    #
    0elunit
    vx
    vy
    @69
    cc0
    @26
    @26
    @35
    @77
    cP
    vx
    vs
    weq
    #
    @31
    cc0
    wceq
    #
    wa
    #
    @29
    @72
    @32
    @34
    @74
    @76
    @103
    @27
    @69
    @28
    cle
    @101
    @102
    simpl
    #
    breq1d
    @103
    @30
    @73
    @31
    cc0
    cM
    @103
    @27
    @69
    c2
    cmul
    @104
    oveq2d
    #
    @101
    @102
    simpr
    #
    oveq12d
    @103
    @33
    @75
    @31
    cc0
    cN
    @103
    @30
    @73
    c1
    cmin
    @105
    oveq1d
    @106
    oveq12d
    ifbieq12d
    pcohtpylem.7
    @72
    @74
    @76
    @73
    cc0
    cM
    ovex
    @75
    cc0
    cN
    ovex
    ifex
    ovmpt2a
    sylancl
    wph
    cF
    cG
    cJ
    @69
    @11
    @17
    pcovalg
    3eqtr4d
    @71
    @72
    @84
    @93
    cif
    #
    @72
    @85
    @94
    cif
    #
    @69
    c1
    cP
    co
    #
    @69
    @2
    cfv
    @71
    @72
    @107
    @108
    wceq
    @82
    @84
    @85
    @107
    @108
    @82
    @83
    @86
    @89
    simprd
    @72
    @107
    @84
    wceq
    @71
    @72
    @84
    @93
    iftrue
    adantl
    @72
    @108
    @85
    wceq
    @71
    @72
    @85
    @94
    iftrue
    adantl
    3eqtr4d
    @91
    @93
    @94
    @107
    @108
    @91
    @92
    @95
    @98
    simprd
    @90
    @107
    @93
    wceq
    @71
    @72
    @84
    @93
    iffalse
    adantl
    @90
    @108
    @94
    wceq
    @71
    @72
    @85
    @94
    iffalse
    adantl
    3eqtr4d
    pm2.61dan
    @71
    @70
    c1
    @26
    wcel
    #
    @109
    @107
    wceq
    @100
    1elunit
    vx
    vy
    @69
    c1
    @26
    @26
    @35
    @107
    cP
    @101
    @31
    c1
    wceq
    #
    wa
    #
    @29
    @72
    @32
    @34
    @84
    @93
    @112
    @27
    @69
    @28
    cle
    @101
    @111
    simpl
    #
    breq1d
    @112
    @30
    @73
    @31
    c1
    cM
    @112
    @27
    @69
    c2
    cmul
    @113
    oveq2d
    #
    @101
    @111
    simpr
    #
    oveq12d
    @112
    @33
    @75
    @31
    c1
    cN
    @112
    @30
    @73
    c1
    cmin
    @114
    oveq1d
    @115
    oveq12d
    ifbieq12d
    pcohtpylem.7
    @72
    @84
    @93
    @73
    c1
    cM
    ovex
    @75
    c1
    cN
    ovex
    ifex
    ovmpt2a
    sylancl
    wph
    cH
    cK
    cJ
    @69
    @18
    @19
    pcovalg
    3eqtr4d
    @71
    cc0
    @69
    cM
    co
    #
    @24
    cc0
    @69
    cP
    co
    #
    cc0
    @1
    cfv
    #
    @71
    @116
    @24
    wceq
    c1
    @69
    cM
    co
    @20
    wceq
    wph
    @69
    cF
    cH
    cM
    cJ
    @11
    @18
    pcohtpylem.8
    phtpyi
    simpld
    @71
    @99
    @70
    @117
    @116
    wceq
    0elunit
    @100
    vx
    vy
    cc0
    @69
    @26
    @26
    @35
    @116
    cP
    @27
    cc0
    wceq
    #
    vy
    vs
    weq
    #
    wa
    #
    @35
    @32
    @116
    @121
    @29
    @32
    @34
    @121
    @27
    cc0
    @28
    cle
    @119
    @120
    simpl
    #
    @46
    syl6eqbr
    iftrued
    @121
    @30
    cc0
    @31
    @69
    cM
    @121
    @30
    c2
    cc0
    cmul
    co
    cc0
    @121
    @27
    cc0
    c2
    cmul
    @122
    oveq2d
    2t0e0
    syl6eq
    @119
    @120
    simpr
    oveq12d
    eqtrd
    pcohtpylem.7
    cc0
    @69
    cM
    ovex
    ovmpt2a
    sylancr
    wph
    @118
    @24
    wceq
    @70
    wph
    cF
    cG
    cJ
    @11
    @17
    pco0
    adantr
    3eqtr4d
    @71
    c1
    @69
    cN
    co
    #
    @25
    c1
    @69
    cP
    co
    #
    c1
    @1
    cfv
    #
    @71
    cc0
    @69
    cN
    co
    @21
    wceq
    @123
    @25
    wceq
    wph
    @69
    cG
    cK
    cN
    cJ
    @17
    @19
    pcohtpylem.9
    phtpyi
    simprd
    @71
    @110
    @70
    @124
    @123
    wceq
    1elunit
    @100
    vx
    vy
    c1
    @69
    @26
    @26
    @35
    @123
    cP
    @27
    c1
    wceq
    #
    @120
    wa
    #
    @35
    @34
    @123
    @127
    @29
    @32
    @34
    @127
    @29
    c1
    @28
    cle
    wbr
    #
    @28
    c1
    clt
    wbr
    @128
    wn
    halflt1
    @28
    c1
    halfre
    1re
    ltnlei
    mpbi
    @127
    @27
    c1
    @28
    cle
    @126
    @120
    simpl
    #
    breq1d
    mtbiri
    iffalsed
    @127
    @33
    c1
    @31
    @69
    cN
    @127
    @33
    c2
    c1
    cmin
    co
    c1
    @127
    @30
    c2
    c1
    cmin
    @127
    @30
    c2
    c1
    cmul
    co
    c2
    @127
    @27
    c1
    c2
    cmul
    @129
    oveq2d
    2t1e2
    syl6eq
    oveq1d
    2m1e1
    syl6eq
    @126
    @120
    simpr
    oveq12d
    eqtrd
    pcohtpylem.7
    c1
    @69
    cN
    ovex
    ovmpt2a
    sylancr
    wph
    @125
    @25
    wceq
    @70
    wph
    cF
    cG
    cJ
    @11
    @17
    pco1
    adantr
    3eqtr4d
    isphtpy2d
end
