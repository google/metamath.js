include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "chash.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cen.mm"
include "wceq.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "1zzd.mm"
include "cuz.mm"
include "eluzelz.mm"
include "syl.mm"
include "zsubcld.mm"
include "zred.mm"
include "nndivred.mm"
include "flcld.mm"
include "peano2zm.mm"
include "fzen.mm"
include "syl3anc.mm"
include "cc.mm"
include "ax-1cn.mm"
include "zcnd.mm"
include "addcom.mm"
include "sylancr.mm"
include "npcand.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "cmul.mm"
include "ovexd.mm"
include "cfn.mm"
include "cvv.mm"
include "fzfi.mm"
include "rabexg.mm"
include "mp1i.mm"
include "wa.mm"
include "cle.mm"
include "clt.mm"
include "elfzle1.mm"
include "adantl.mm"
include "wb.mm"
include "elfzelz.mm"
include "zltp1le.mm"
include "syl2an.mm"
include "mpbird.mm"
include "cr.mm"
include "fllt.mm"
include "cc0.mm"
include "adantr.mm"
include "nnred.mm"
include "nngt0d.mm"
include "jca.mm"
include "ltdivmul2.mm"
include "mpbid.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "ltsubaddd.mm"
include "zaddcld.mm"
include "zlem1lt.mm"
include "syl2anc.mm"
include "elfzle2.mm"
include "flge.mm"
include "lemuldiv.mm"
include "leaddsub.mm"
include "elfz.mm"
include "mpbir2and.mm"
include "dvdsmul2.mm"
include "pncand.mm"
include "breqtrrd.mm"
include "oveq1.mm"
include "breq2d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ad2antrl.mm"
include "ltsub1dd.mm"
include "ltdiv1.mm"
include "simprr.mm"
include "wne.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "lesub1dd.mm"
include "lediv1.mm"
include "peano2zd.mm"
include "syl5bi.mm"
include "anbi2i.mm"
include "adantrl.mm"
include "adantrr.mm"
include "nncnd.mm"
include "divmul3d.mm"
include "subadd2d.mm"
include "bitrd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "sylan2b.mm"
include "en3d.mm"
include "entr.mm"
include "wss.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashen.mm"
include "sylibr.mm"
include "cn0.mm"
include "eluzle.mm"
include "zre.mm"
include "lesub1.mm"
include "syl3an.mm"
include "flword2.mm"
include "uznn0sub.mm"
include "hashfz1.mm"
include "3syl.mm"
include "eqtr3d.mm"

theorem hashdvds
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vy: setvar y
  let vz: setvar z
  assume hashdvds.1: |- ( ph -> N e. NN )
  assume hashdvds.2: |- ( ph -> A e. ZZ )
  assume hashdvds.3: |- ( ph -> B e. ( ZZ>= ` ( A - 1 ) ) )
  assume hashdvds.4: |- ( ph -> C e. ZZ )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint N x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint N y
  disjoint N z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( # ` { x e. ( A ... B ) | N || ( x - C ) } ) = ( ( |_ ` ( ( B - C ) / N ) ) - ( |_ ` ( ( ( A - 1 ) - C ) / N ) ) ) )

  proof
    wph
    c1
    cB
    cC
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cA
    c1
    cmin
    co
    #
    cC
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    #
    cfz
    co
    #
    chash
    cfv
    #
    cN
    vx
    cv
    #
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    vx
    cA
    cB
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    @7
    wph
    @8
    @14
    cen
    wbr
    #
    @9
    @15
    wceq
    #
    wph
    @8
    @6
    c1
    caddc
    co
    #
    @2
    cfz
    co
    #
    cen
    wbr
    @19
    @14
    cen
    wbr
    @16
    wph
    @8
    c1
    @6
    caddc
    co
    #
    @7
    @6
    caddc
    co
    #
    cfz
    co
    #
    @19
    cen
    wph
    c1
    cz
    wcel
    @7
    cz
    wcel
    @6
    cz
    wcel
    #
    @8
    @22
    cen
    wbr
    wph
    1zzd
    wph
    @2
    @6
    wph
    @1
    wph
    @0
    cN
    wph
    @0
    wph
    cB
    cC
    wph
    cB
    @3
    cuz
    cfv
    wcel
    #
    cB
    cz
    wcel
    #
    hashdvds.3
    @3
    cB
    eluzelz
    syl
    #
    hashdvds.4
    zsubcld
    zred
    #
    hashdvds.1
    nndivred
    #
    flcld
    #
    wph
    @5
    wph
    @4
    cN
    wph
    @4
    wph
    @3
    cC
    wph
    cA
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    hashdvds.2
    cA
    peano2zm
    syl
    #
    hashdvds.4
    zsubcld
    zred
    #
    hashdvds.1
    nndivred
    #
    flcld
    #
    zsubcld
    @35
    @6
    c1
    @7
    fzen
    syl3anc
    wph
    @20
    @18
    @21
    @2
    cfz
    wph
    c1
    cc
    wcel
    @6
    cc
    wcel
    @20
    @18
    wceq
    ax-1cn
    wph
    @6
    @35
    zcnd
    #
    c1
    @6
    addcom
    sylancr
    wph
    @2
    @6
    wph
    @2
    @29
    zcnd
    @36
    npcand
    oveq12d
    breqtrd
    wph
    vz
    vy
    @19
    @14
    vz
    cv
    #
    cN
    cmul
    co
    #
    cC
    caddc
    co
    #
    vy
    cv
    #
    cC
    cmin
    co
    #
    cN
    cdiv
    co
    #
    wph
    @18
    @2
    cfz
    ovexd
    @13
    cfn
    wcel
    #
    @14
    cvv
    wcel
    wph
    cA
    cB
    fzfi
    #
    @12
    vx
    @13
    cfn
    rabexg
    mp1i
    wph
    @37
    @19
    wcel
    #
    @39
    @14
    wcel
    #
    wph
    @45
    wa
    #
    @39
    @13
    wcel
    #
    cN
    @39
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    @46
    @47
    @48
    cA
    @39
    cle
    wbr
    #
    @39
    cB
    cle
    wbr
    #
    @47
    @51
    @3
    @39
    clt
    wbr
    #
    @47
    @4
    @38
    clt
    wbr
    #
    @53
    @47
    @5
    @37
    clt
    wbr
    #
    @54
    @47
    @55
    @6
    @37
    clt
    wbr
    #
    @47
    @56
    @18
    @37
    cle
    wbr
    #
    @45
    @57
    wph
    @37
    @18
    @2
    elfzle1
    adantl
    wph
    @23
    @37
    cz
    wcel
    #
    @56
    @57
    wb
    @45
    @35
    @37
    @18
    @2
    elfzelz
    #
    @6
    @37
    zltp1le
    syl2an
    mpbird
    wph
    @5
    cr
    wcel
    #
    @58
    @55
    @56
    wb
    @45
    @34
    @59
    @5
    @37
    fllt
    syl2an
    mpbird
    @47
    @4
    cr
    wcel
    #
    @37
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    wa
    #
    @55
    @54
    wb
    wph
    @61
    @45
    @33
    adantr
    @47
    @37
    @45
    @58
    wph
    @59
    adantl
    #
    zred
    #
    wph
    @65
    @45
    wph
    @63
    @64
    wph
    cN
    hashdvds.1
    nnred
    wph
    cN
    hashdvds.1
    nngt0d
    jca
    #
    adantr
    #
    @4
    @37
    cN
    ltdivmul2
    syl3anc
    mpbid
    @47
    @3
    cC
    @38
    wph
    @3
    cr
    wcel
    #
    @45
    wph
    @3
    @32
    zred
    #
    adantr
    wph
    cC
    cr
    wcel
    #
    @45
    wph
    cC
    hashdvds.4
    zred
    #
    adantr
    #
    @47
    @38
    @47
    @37
    cN
    @66
    wph
    cN
    cz
    wcel
    #
    @45
    wph
    cN
    hashdvds.1
    nnzd
    #
    adantr
    #
    zmulcld
    #
    zred
    #
    ltsubaddd
    mpbid
    @47
    @30
    @39
    cz
    wcel
    #
    @51
    @53
    wb
    wph
    @30
    @45
    hashdvds.2
    adantr
    #
    @47
    @38
    cC
    @78
    wph
    cC
    cz
    wcel
    #
    @45
    hashdvds.4
    adantr
    zaddcld
    #
    cA
    @39
    zlem1lt
    syl2anc
    mpbird
    @47
    @52
    @38
    @0
    cle
    wbr
    #
    @47
    @84
    @37
    @1
    cle
    wbr
    #
    @47
    @85
    @37
    @2
    cle
    wbr
    #
    @45
    @86
    wph
    @37
    @18
    @2
    elfzle2
    adantl
    wph
    @1
    cr
    wcel
    #
    @58
    @85
    @86
    wb
    @45
    @28
    @59
    @1
    @37
    flge
    syl2an
    mpbird
    @47
    @62
    @0
    cr
    wcel
    #
    @65
    @84
    @85
    wb
    @67
    wph
    @88
    @45
    @27
    adantr
    @69
    @37
    @0
    cN
    lemuldiv
    syl3anc
    mpbird
    @47
    @38
    cr
    wcel
    @72
    cB
    cr
    wcel
    #
    @52
    @84
    wb
    @79
    @74
    wph
    @89
    @45
    wph
    cB
    @26
    zred
    #
    adantr
    @38
    cC
    cB
    leaddsub
    syl3anc
    mpbird
    @47
    @80
    @30
    @25
    @48
    @51
    @52
    wa
    wb
    @83
    @81
    wph
    @25
    @45
    @26
    adantr
    @39
    cA
    cB
    elfz
    syl3anc
    mpbir2and
    @47
    cN
    @38
    @49
    cdvds
    @47
    @58
    @75
    cN
    @38
    cdvds
    wbr
    @66
    @77
    @37
    cN
    dvdsmul2
    syl2anc
    @47
    @38
    cC
    @47
    @38
    @78
    zcnd
    #
    wph
    cC
    cc
    wcel
    #
    @45
    wph
    cC
    hashdvds.4
    zcnd
    #
    adantr
    pncand
    breqtrrd
    @12
    @50
    vx
    @39
    @13
    @10
    @39
    wceq
    @11
    @49
    cN
    cdvds
    @10
    @39
    cC
    cmin
    oveq1
    breq2d
    elrab
    sylanbrc
    ex
    @40
    @14
    wcel
    #
    @40
    @13
    wcel
    #
    cN
    @41
    cdvds
    wbr
    #
    wa
    #
    wph
    @42
    @19
    wcel
    #
    @12
    @96
    vx
    @40
    @13
    @10
    @40
    wceq
    @11
    @41
    cN
    cdvds
    @10
    @40
    cC
    cmin
    oveq1
    breq2d
    elrab
    #
    wph
    @97
    @98
    wph
    @97
    wa
    #
    @98
    @18
    @42
    cle
    wbr
    #
    @42
    @2
    cle
    wbr
    #
    @100
    @6
    @42
    clt
    wbr
    #
    @101
    @100
    @5
    @42
    clt
    wbr
    #
    @103
    @100
    @4
    @41
    clt
    wbr
    #
    @104
    @100
    @3
    @40
    cC
    wph
    @70
    @97
    @71
    adantr
    @100
    @40
    @95
    @40
    cz
    wcel
    #
    wph
    @96
    @40
    cA
    cB
    elfzelz
    ad2antrl
    #
    zred
    #
    wph
    @72
    @97
    @73
    adantr
    #
    @100
    cA
    @40
    cle
    wbr
    #
    @3
    @40
    clt
    wbr
    #
    @95
    @110
    wph
    @96
    @40
    cA
    cB
    elfzle1
    ad2antrl
    @100
    @30
    @106
    @110
    @111
    wb
    wph
    @30
    @97
    hashdvds.2
    adantr
    @107
    cA
    @40
    zlem1lt
    syl2anc
    mpbid
    ltsub1dd
    @100
    @61
    @41
    cr
    wcel
    #
    @65
    @105
    @104
    wb
    wph
    @61
    @97
    @33
    adantr
    @100
    @41
    @100
    @40
    cC
    @107
    wph
    @82
    @97
    hashdvds.4
    adantr
    zsubcld
    #
    zred
    #
    wph
    @65
    @97
    @68
    adantr
    #
    @4
    @41
    cN
    ltdiv1
    syl3anc
    mpbid
    @100
    @60
    @42
    cz
    wcel
    #
    @104
    @103
    wb
    wph
    @60
    @97
    @34
    adantr
    @100
    @96
    @116
    wph
    @95
    @96
    simprr
    @100
    @75
    cN
    cc0
    wne
    #
    @41
    cz
    wcel
    @96
    @116
    wb
    wph
    @75
    @97
    @76
    adantr
    wph
    @117
    @97
    wph
    cN
    hashdvds.1
    nnne0d
    #
    adantr
    @113
    cN
    @41
    dvdsval2
    syl3anc
    mpbid
    #
    @5
    @42
    fllt
    syl2anc
    mpbid
    @100
    @23
    @116
    @103
    @101
    wb
    wph
    @23
    @97
    @35
    adantr
    @119
    @6
    @42
    zltp1le
    syl2anc
    mpbid
    @100
    @42
    @1
    cle
    wbr
    #
    @102
    @100
    @41
    @0
    cle
    wbr
    #
    @120
    @100
    @40
    cB
    cC
    @108
    wph
    @89
    @97
    @90
    adantr
    @109
    @95
    @40
    cB
    cle
    wbr
    wph
    @96
    @40
    cA
    cB
    elfzle2
    ad2antrl
    lesub1dd
    @100
    @112
    @88
    @65
    @121
    @120
    wb
    @114
    wph
    @88
    @97
    @27
    adantr
    @115
    @41
    @0
    cN
    lediv1
    syl3anc
    mpbid
    @100
    @87
    @116
    @120
    @102
    wb
    wph
    @87
    @97
    @28
    adantr
    @119
    @1
    @42
    flge
    syl2anc
    mpbid
    @100
    @116
    @18
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @98
    @101
    @102
    wa
    wb
    @119
    wph
    @122
    @97
    wph
    @6
    @35
    peano2zd
    adantr
    wph
    @123
    @97
    @29
    adantr
    @42
    @18
    @2
    elfz
    syl3anc
    mpbir2and
    ex
    syl5bi
    wph
    @45
    @94
    wa
    #
    @37
    @42
    wceq
    #
    @40
    @39
    wceq
    #
    wb
    #
    @124
    wph
    @45
    @97
    wa
    #
    @127
    @94
    @97
    @45
    @99
    anbi2i
    wph
    @128
    wa
    #
    @42
    @37
    wceq
    #
    @39
    @40
    wceq
    #
    @125
    @126
    @129
    @130
    @41
    @38
    wceq
    @131
    @129
    @41
    @37
    cN
    wph
    @97
    @41
    cc
    wcel
    @45
    @100
    @41
    @113
    zcnd
    adantrl
    wph
    @45
    @37
    cc
    wcel
    @97
    @47
    @37
    @66
    zcnd
    adantrr
    wph
    cN
    cc
    wcel
    @128
    wph
    cN
    hashdvds.1
    nncnd
    adantr
    wph
    @117
    @128
    @118
    adantr
    divmul3d
    @129
    @40
    cC
    @38
    wph
    @97
    @40
    cc
    wcel
    @45
    @100
    @40
    @107
    zcnd
    adantrl
    wph
    @92
    @128
    @93
    adantr
    wph
    @45
    @38
    cc
    wcel
    @97
    @91
    adantrr
    subadd2d
    bitrd
    @37
    @42
    eqcom
    @40
    @39
    eqcom
    3bitr4g
    sylan2b
    ex
    en3d
    @8
    @19
    @14
    entr
    syl2anc
    @8
    cfn
    wcel
    @14
    cfn
    wcel
    #
    @17
    @16
    wb
    c1
    @7
    fzfi
    @43
    @14
    @13
    wss
    @132
    @44
    @12
    vx
    @13
    ssrab2
    @13
    @14
    ssfi
    mp2an
    @8
    @14
    hashen
    mp2an
    sylibr
    wph
    @2
    @6
    cuz
    cfv
    wcel
    #
    @7
    cn0
    wcel
    @9
    @7
    wceq
    wph
    @60
    @87
    @5
    @1
    cle
    wbr
    #
    @133
    @34
    @28
    wph
    @4
    @0
    cle
    wbr
    #
    @134
    wph
    @3
    cB
    cle
    wbr
    #
    @135
    wph
    @24
    @136
    hashdvds.3
    @3
    cB
    eluzle
    syl
    wph
    @31
    @25
    @82
    @136
    @135
    wb
    #
    @32
    @26
    hashdvds.4
    @31
    @70
    @25
    @89
    @82
    @72
    @137
    @3
    zre
    cB
    zre
    cC
    zre
    @3
    cB
    cC
    lesub1
    syl3an
    syl3anc
    mpbid
    wph
    @61
    @88
    @65
    @135
    @134
    wb
    @33
    @27
    @68
    @4
    @0
    cN
    lediv1
    syl3anc
    mpbid
    @5
    @1
    flword2
    syl3anc
    @6
    @2
    uznn0sub
    @7
    hashfz1
    3syl
    eqtr3d
end
