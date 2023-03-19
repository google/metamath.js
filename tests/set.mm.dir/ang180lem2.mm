include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "c2.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cpi.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "c3.mm"
include "2cn.mm"
include "1re.mm"
include "rehalfcli.mm"
include "recni.mm"
include "negsubdii.mm"
include "c4.mm"
include "4d2e2.mm"
include "oveq1i.mm"
include "wa.mm"
include "wceq.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "2cnne0.mm"
include "divsubdir.mm"
include "mp3an.mm"
include "3cn.mm"
include "addcomi.mm"
include "df-4.mm"
include "eqtr4i.mm"
include "subaddrii.mm"
include "eqtr3i.mm"
include "negeqi.mm"
include "3re.mm"
include "picn.mm"
include "mulassi.mm"
include "2ne0.mm"
include "divcan1i.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "mulneg1i.mm"
include "mulneg2i.mm"
include "3eqtr4i.mm"
include "cim.mm"
include "cfv.mm"
include "clog.mm"
include "cr.mm"
include "renegcli.mm"
include "a1i.mm"
include "simp1.mm"
include "subcl.mm"
include "sylancr.mm"
include "simp3.mm"
include "necomd.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "reccld.mm"
include "recne0d.mm"
include "logcld.mm"
include "sylancl.mm"
include "simp2.mm"
include "divcld.mm"
include "divne0d.mm"
include "addcld.mm"
include "imcld.mm"
include "logcl.mm"
include "3adant3.mm"
include "cle.mm"
include "logimcld.mm"
include "simpld.mm"
include "lt2addd.mm"
include "negpicn.mm"
include "2timesi.mm"
include "imaddd.mm"
include "3brtr4d.mm"
include "logimcl.mm"
include "df-3.mm"
include "adddiri.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "syl5eq.mm"
include "cre.mm"
include "syl5eqel.mm"
include "imval.mm"
include "syl.mm"
include "cz.mm"
include "ang180lem1.mm"
include "simprd.mm"
include "rered.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "syl5eqbr.mm"
include "2pos.mm"
include "pipos.mm"
include "mulgt0ii.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "gt0ne0ii.mm"
include "redivcld.mm"
include "ltaddsubd.mm"
include "syl6breqr.mm"
include "le2addd.mm"
include "eqtr3d.mm"
include "subid1i.mm"
include "eqnetri.mm"
include "crp.mm"
include "negsub.mm"
include "adantr.mm"
include "1rp.mm"
include "oveq12d.mm"
include "recnd.mm"
include "addsub4d.mm"
include "ax-icn.mm"
include "ine0.mm"
include "biimpar.mm"
include "resubcl.mm"
include "subge0.mm"
include "add20.mm"
include "syl22anc.mm"
include "biimpa.mm"
include "syldan.mm"
include "eqcomd.mm"
include "lognegb.mm"
include "rpaddcl.mm"
include "eqeltrrd.mm"
include "rpreccld.mm"
include "relogcld.mm"
include "negsubdi2.mm"
include "oveq1d.mm"
include "div2negd.mm"
include "rpdivcld.mm"
include "readdcld.mm"
include "reim0d.mm"
include "oveq2d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpi.mm"
include "ltlen.mm"
include "mpbir2and.mm"
include "ltdivmul2.mm"
include "divdiri.mm"
include "2div2e1.mm"
include "syl6breq.mm"
include "ltsubaddd.mm"
include "jca.mm"

theorem ang180lem2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cT: class T
  let cF: class F
  let cN: class N
  let cB: class B
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume ang180lem1.2: |- T = ( ( ( log ` ( 1 / ( 1 - A ) ) ) + ( log ` ( ( A - 1 ) / A ) ) ) + ( log ` A ) )
  assume ang180lem1.3: |- N = ( ( ( T / _i ) / ( 2 x. _pi ) ) - ( 1 / 2 ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> ( -u 2 < N /\ N < 1 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    c1
    wne
    #
    w3a
    #
    c2
    cneg
    #
    cN
    clt
    wbr
    cN
    c1
    clt
    wbr
    @3
    @4
    cT
    ci
    cdiv
    co
    #
    c2
    cpi
    cmul
    co
    #
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cN
    clt
    @3
    @4
    @8
    caddc
    co
    #
    @7
    clt
    wbr
    @4
    @9
    clt
    wbr
    @3
    @10
    c3
    c2
    cdiv
    co
    #
    cneg
    #
    @7
    clt
    c2
    @8
    cmin
    co
    #
    cneg
    @10
    @12
    c2
    @8
    2cn
    @8
    c1
    1re
    rehalfcli
    #
    recni
    negsubdii
    @13
    @11
    c4
    c2
    cdiv
    co
    #
    @8
    cmin
    co
    #
    @13
    @11
    @15
    c2
    @8
    cmin
    4d2e2
    oveq1i
    c4
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @16
    @11
    c4
    cc
    wcel
    c1
    cc
    wcel
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @18
    @16
    wceq
    4cn
    ax-1cn
    2cnne0
    c4
    c1
    c2
    divsubdir
    mp3an
    @17
    c3
    c2
    cdiv
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    c1
    c3
    caddc
    co
    c3
    c1
    caddc
    co
    c4
    c1
    c3
    ax-1cn
    3cn
    addcomi
    df-4
    eqtr4i
    subaddrii
    oveq1i
    eqtr3i
    eqtr3i
    negeqi
    eqtr3i
    @3
    @12
    @6
    cmul
    co
    #
    @5
    clt
    wbr
    #
    @12
    @7
    clt
    wbr
    #
    @3
    @20
    c3
    cpi
    cneg
    #
    cmul
    co
    #
    @5
    clt
    @11
    @6
    cmul
    co
    #
    cneg
    c3
    cpi
    cmul
    co
    #
    cneg
    @20
    @24
    @25
    @26
    @11
    c2
    cmul
    co
    #
    cpi
    cmul
    co
    @25
    @26
    @11
    c2
    cpi
    @11
    c3
    3re
    rehalfcli
    #
    recni
    #
    2cn
    picn
    mulassi
    @27
    c3
    cpi
    cmul
    c3
    c2
    3cn
    2cn
    2ne0
    divcan1i
    oveq1i
    eqtr3i
    #
    negeqi
    @11
    @6
    @29
    @6
    c2
    cpi
    2re
    pire
    remulcli
    #
    recni
    #
    mulneg1i
    c3
    cpi
    3cn
    picn
    mulneg2i
    3eqtr4i
    @3
    @24
    cT
    cim
    cfv
    #
    @5
    clt
    @3
    c2
    @23
    cmul
    co
    #
    @23
    caddc
    co
    #
    c1
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    clog
    cfv
    #
    cA
    c1
    cmin
    co
    #
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    caddc
    co
    #
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
    caddc
    co
    #
    @24
    @33
    clt
    @3
    @34
    @23
    @43
    @45
    @34
    cr
    wcel
    @3
    c2
    @23
    2re
    cpi
    pire
    renegcli
    #
    remulcli
    a1i
    @23
    cr
    wcel
    @3
    @47
    a1i
    #
    @3
    @42
    @3
    @38
    @41
    @3
    @37
    @3
    @36
    @3
    @19
    @0
    @36
    cc
    wcel
    ax-1cn
    @0
    @1
    @2
    simp1
    #
    c1
    cA
    subcl
    sylancr
    #
    @3
    @36
    cc0
    wne
    c1
    cA
    wne
    @3
    cA
    c1
    @0
    @1
    @2
    simp3
    #
    necomd
    @3
    @36
    cc0
    c1
    cA
    @3
    @19
    @0
    @36
    cc0
    wceq
    c1
    cA
    wceq
    wb
    ax-1cn
    @49
    c1
    cA
    subeq0
    sylancr
    necon3bid
    mpbird
    #
    reccld
    #
    @3
    @36
    @50
    @52
    recne0d
    #
    logcld
    #
    @3
    @40
    @3
    @39
    cA
    @3
    @0
    @19
    @39
    cc
    wcel
    @49
    ax-1cn
    cA
    c1
    subcl
    sylancl
    #
    @49
    @0
    @1
    @2
    simp2
    #
    divcld
    #
    @3
    @39
    cA
    @56
    @49
    @3
    @39
    cc0
    wne
    @2
    @51
    @3
    @39
    cc0
    cA
    c1
    @3
    @0
    @19
    @39
    cc0
    wceq
    cA
    c1
    wceq
    wb
    @49
    ax-1cn
    cA
    c1
    subeq0
    sylancl
    necon3bid
    mpbird
    @57
    divne0d
    #
    logcld
    #
    addcld
    #
    imcld
    #
    @3
    @44
    @0
    @1
    @44
    cc
    wcel
    @2
    cA
    logcl
    3adant3
    #
    imcld
    #
    @3
    @23
    @23
    caddc
    co
    #
    @38
    cim
    cfv
    #
    @41
    cim
    cfv
    #
    caddc
    co
    #
    @34
    @43
    clt
    @3
    @23
    @23
    @66
    @67
    @48
    @48
    @3
    @38
    @55
    imcld
    #
    @3
    @41
    @60
    imcld
    #
    @3
    @23
    @66
    clt
    wbr
    #
    @66
    cpi
    cle
    wbr
    #
    @3
    @37
    @53
    @54
    logimcld
    #
    simpld
    @3
    @23
    @67
    clt
    wbr
    #
    @67
    cpi
    cle
    wbr
    #
    @3
    @40
    @58
    @59
    logimcld
    #
    simpld
    lt2addd
    @34
    @65
    wceq
    @3
    @23
    negpicn
    2timesi
    a1i
    @3
    @38
    @41
    @55
    @60
    imaddd
    #
    3brtr4d
    @3
    @23
    @45
    clt
    wbr
    #
    @45
    cpi
    cle
    wbr
    #
    @0
    @1
    @78
    @79
    wa
    @2
    cA
    logimcl
    3adant3
    #
    simpld
    lt2addd
    @24
    @35
    wceq
    @3
    @24
    c2
    c1
    caddc
    co
    #
    @23
    cmul
    co
    @34
    c1
    @23
    cmul
    co
    #
    caddc
    co
    @35
    c3
    @81
    @23
    cmul
    df-3
    oveq1i
    c2
    c1
    @23
    2cn
    ax-1cn
    negpicn
    adddiri
    @82
    @23
    @34
    caddc
    @23
    negpicn
    mulid2i
    oveq2i
    3eqtri
    a1i
    @3
    @33
    @42
    @44
    caddc
    co
    #
    cim
    cfv
    @46
    cT
    @83
    cim
    ang180lem1.2
    fveq2i
    @3
    @42
    @44
    @61
    @63
    imaddd
    syl5eq
    #
    3brtr4d
    @3
    @33
    @5
    cre
    cfv
    #
    @5
    @3
    cT
    cc
    wcel
    @33
    @85
    wceq
    @3
    cT
    @83
    cc
    ang180lem1.2
    @3
    @42
    @44
    @61
    @63
    addcld
    syl5eqel
    #
    cT
    imval
    syl
    @3
    @5
    @3
    cN
    cz
    wcel
    @5
    cr
    wcel
    #
    vx
    vy
    cA
    cT
    cF
    cN
    ang.1
    ang180lem1.2
    ang180lem1.3
    ang180lem1
    simprd
    #
    rered
    eqtrd
    #
    breqtrd
    syl5eqbr
    @3
    @12
    cr
    wcel
    #
    @87
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    @21
    @22
    wb
    @90
    @3
    @11
    @28
    renegcli
    a1i
    @88
    @91
    @3
    @31
    a1i
    #
    @92
    @3
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    #
    a1i
    #
    @12
    @5
    @6
    ltmuldiv
    syl112anc
    mpbid
    syl5eqbr
    @3
    @4
    @8
    @7
    @4
    cr
    wcel
    @3
    c2
    2re
    renegcli
    a1i
    @8
    cr
    wcel
    @3
    @14
    a1i
    #
    @3
    @5
    @6
    @88
    @93
    @6
    cc0
    wne
    @3
    @6
    @31
    @94
    gt0ne0ii
    #
    a1i
    redivcld
    #
    ltaddsubd
    mpbid
    ang180lem1.3
    syl6breqr
    @3
    cN
    @9
    c1
    clt
    ang180lem1.3
    @3
    @9
    c1
    clt
    wbr
    @7
    c1
    @8
    caddc
    co
    #
    clt
    wbr
    @3
    @7
    @11
    @99
    clt
    @3
    @7
    @11
    clt
    wbr
    #
    @5
    @25
    clt
    wbr
    #
    @3
    @5
    @26
    @25
    clt
    @3
    @5
    @26
    clt
    wbr
    #
    @5
    @26
    cle
    wbr
    #
    @26
    @5
    wne
    #
    @3
    @46
    @6
    cpi
    caddc
    co
    #
    @5
    @26
    cle
    @3
    @43
    @45
    @6
    cpi
    @62
    @64
    @93
    cpi
    cr
    wcel
    #
    @3
    pire
    a1i
    #
    @3
    @68
    cpi
    cpi
    caddc
    co
    #
    @43
    @6
    cle
    @3
    @66
    @67
    cpi
    cpi
    @69
    @70
    @107
    @107
    @3
    @71
    @72
    @73
    simprd
    @3
    @74
    @75
    @76
    simprd
    le2addd
    @77
    @6
    @108
    wceq
    @3
    cpi
    picn
    2timesi
    a1i
    3brtr4d
    #
    @3
    @78
    @79
    @80
    simprd
    #
    le2addd
    @3
    @33
    @5
    @46
    @89
    @84
    eqtr3d
    #
    @26
    @105
    wceq
    @3
    @26
    @81
    cpi
    cmul
    co
    @6
    c1
    cpi
    cmul
    co
    #
    caddc
    co
    @105
    c3
    @81
    cpi
    cmul
    df-3
    oveq1i
    c2
    c1
    cpi
    2cn
    ax-1cn
    picn
    adddiri
    @112
    cpi
    @6
    caddc
    cpi
    picn
    mulid2i
    oveq2i
    3eqtri
    a1i
    #
    3brtr4d
    @3
    @6
    cc0
    cmin
    co
    #
    cc0
    wne
    @104
    @114
    @6
    cc0
    @6
    @32
    subid1i
    @97
    eqnetri
    @3
    @26
    @5
    @114
    cc0
    @3
    @26
    @5
    wceq
    #
    @114
    cc0
    wceq
    @3
    @115
    wa
    #
    @6
    @43
    cmin
    co
    #
    @114
    cc0
    @116
    @43
    cc0
    @6
    cmin
    @116
    @42
    @116
    @38
    @41
    @116
    @37
    @116
    @36
    @116
    c1
    cA
    cneg
    #
    caddc
    co
    #
    @36
    crp
    @3
    @119
    @36
    wceq
    #
    @115
    @3
    @19
    @0
    @120
    ax-1cn
    @49
    c1
    cA
    negsub
    sylancr
    adantr
    @116
    c1
    crp
    wcel
    @118
    crp
    wcel
    #
    @119
    crp
    wcel
    1rp
    @116
    @121
    @45
    cpi
    wceq
    #
    @116
    cpi
    @45
    @116
    cpi
    @45
    cmin
    co
    #
    cc0
    wceq
    #
    cpi
    @45
    wceq
    #
    @116
    @117
    cc0
    wceq
    #
    @124
    @3
    @115
    @117
    @123
    caddc
    co
    #
    cc0
    wceq
    #
    @126
    @124
    wa
    #
    @116
    @26
    @5
    cmin
    co
    #
    @127
    cc0
    @3
    @130
    @127
    wceq
    @115
    @3
    @130
    @105
    @46
    cmin
    co
    @127
    @3
    @26
    @105
    @5
    @46
    cmin
    @113
    @111
    oveq12d
    @3
    @6
    cpi
    @43
    @45
    @6
    cc
    wcel
    @3
    @32
    a1i
    cpi
    cc
    wcel
    #
    @3
    picn
    a1i
    @3
    @43
    @62
    recnd
    @3
    @45
    @64
    recnd
    #
    addsub4d
    eqtrd
    adantr
    @3
    @130
    cc0
    wceq
    #
    @115
    @3
    @26
    cc
    wcel
    @5
    cc
    wcel
    @133
    @115
    wb
    @26
    c3
    cpi
    3re
    pire
    remulcli
    #
    recni
    @3
    cT
    ci
    @86
    ci
    cc
    wcel
    @3
    ax-icn
    a1i
    ci
    cc0
    wne
    @3
    ine0
    a1i
    divcld
    @26
    @5
    subeq0
    sylancr
    biimpar
    eqtr3d
    @3
    @128
    @129
    @3
    @117
    cr
    wcel
    #
    cc0
    @117
    cle
    wbr
    #
    @123
    cr
    wcel
    #
    cc0
    @123
    cle
    wbr
    #
    @128
    @129
    wb
    @3
    @91
    @43
    cr
    wcel
    #
    @135
    @31
    @62
    @6
    @43
    resubcl
    sylancr
    @3
    @136
    @43
    @6
    cle
    wbr
    #
    @109
    @3
    @91
    @139
    @136
    @140
    wb
    @31
    @62
    @6
    @43
    subge0
    sylancr
    mpbird
    @3
    @106
    @45
    cr
    wcel
    #
    @137
    pire
    @64
    cpi
    @45
    resubcl
    sylancr
    @3
    @138
    @79
    @110
    @3
    @106
    @141
    @138
    @79
    wb
    pire
    @64
    cpi
    @45
    subge0
    sylancr
    mpbird
    @117
    @123
    add20
    syl22anc
    biimpa
    syldan
    #
    simprd
    @116
    @131
    @45
    cc
    wcel
    #
    @124
    @125
    wb
    picn
    @3
    @143
    @115
    @132
    adantr
    cpi
    @45
    subeq0
    sylancr
    mpbid
    eqcomd
    @3
    @121
    @122
    wb
    #
    @115
    @0
    @1
    @144
    @2
    cA
    lognegb
    3adant3
    adantr
    mpbird
    #
    c1
    @118
    rpaddcl
    sylancr
    eqeltrrd
    #
    rpreccld
    relogcld
    @116
    @40
    @116
    @36
    @118
    cdiv
    co
    #
    @40
    crp
    @3
    @147
    @40
    wceq
    @115
    @3
    @39
    cneg
    #
    @118
    cdiv
    co
    @147
    @40
    @3
    @148
    @36
    @118
    cdiv
    @3
    @0
    @19
    @148
    @36
    wceq
    @49
    ax-1cn
    cA
    c1
    negsubdi2
    sylancl
    oveq1d
    @3
    @39
    cA
    @56
    @49
    @57
    div2negd
    eqtr3d
    adantr
    @116
    @36
    @118
    @146
    @145
    rpdivcld
    eqeltrrd
    relogcld
    readdcld
    reim0d
    oveq2d
    @116
    @126
    @124
    @142
    simpld
    eqtr3d
    ex
    necon3d
    mpi
    @3
    @87
    @26
    cr
    wcel
    @102
    @103
    @104
    wa
    wb
    @88
    @134
    @5
    @26
    ltlen
    sylancl
    mpbir2and
    @30
    syl6breqr
    @3
    @87
    @11
    cr
    wcel
    #
    @91
    @92
    @100
    @101
    wb
    @88
    @149
    @3
    @28
    a1i
    @93
    @95
    @5
    @11
    @6
    ltdivmul2
    syl112anc
    mpbird
    @11
    @81
    c2
    cdiv
    co
    c2
    c2
    cdiv
    co
    #
    @8
    caddc
    co
    @99
    c3
    @81
    c2
    cdiv
    df-3
    oveq1i
    c2
    c1
    c2
    2cn
    ax-1cn
    2cn
    2ne0
    divdiri
    @150
    c1
    @8
    caddc
    2div2e1
    oveq1i
    3eqtri
    syl6breq
    @3
    @7
    @8
    c1
    @98
    @96
    c1
    cr
    wcel
    @3
    1re
    a1i
    ltsubaddd
    mpbird
    syl5eqbr
    jca
end
