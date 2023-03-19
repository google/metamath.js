include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "caddc.mm"
include "clt.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "sumex.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "cmin.mm"
include "fzfid.mm"
include "wa.mm"
include "cr.mm"
include "rpred.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "w3a.mm"
include "elfzuz.mm"
include "syl.mm"
include "eluz2.mm"
include "sylib.mm"
include "simp2d.mm"
include "zred.mm"
include "nnred.mm"
include "resubcld.mm"
include "1red.mm"
include "readdcld.mm"
include "nndivred.mm"
include "3re.mm"
include "a1i.mm"
include "wne.mm"
include "3ne0.mm"
include "rereccld.mm"
include "wss.mm"
include "elfzelz.mm"
include "peano2zm.mm"
include "3syl.mm"
include "nnzd.mm"
include "lem1d.mm"
include "elfzuz3.mm"
include "eluzle.mm"
include "letrd.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "sselda.mm"
include "syldan.mm"
include "cin.mm"
include "c0.mm"
include "ltm1d.mm"
include "fzdisj.mm"
include "cun.mm"
include "fzssp1.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "oveq2d.mm"
include "syl5sseq.mm"
include "wb.mm"
include "1zzd.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "sseldd.mm"
include "fzsplit.mm"
include "zcnd.mm"
include "oveq1d.mm"
include "uneq2d.mm"
include "eqtrd.mm"
include "cc.mm"
include "rpcnd.mm"
include "recnd.mm"
include "mulcld.mm"
include "fsumsplit.mm"
include "wf.mm"
include "0zd.mm"
include "0red.mm"
include "0le1.mm"
include "simp3d.mm"
include "fzss1.mm"
include "eluzfz2.mm"
include "ne0i.mm"
include "4syl.mm"
include "cn.mm"
include "rpgt0d.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "fsumlt.mm"
include "chash.mm"
include "cfn.mm"
include "nnne0d.mm"
include "divcld.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "hashfz.mm"
include "breqtrd.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "lemul2.mm"
include "mulid1d.mm"
include "fsumle.mm"
include "0z.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "eluzp1m1.mm"
include "sylancr.mm"
include "subcld.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "mulcomd.mm"
include "leadd1dd.mm"
include "ltletrd.mm"
include "addcld.mm"
include "mul12d.mm"
include "div12d.mm"
include "elfzle1.mm"
include "suble0d.mm"
include "mpbird.mm"
include "leadd2dd.mm"
include "addsub12d.mm"
include "addcomd.mm"
include "addid1d.mm"
include "3brtr3d.mm"
include "nngt0d.mm"
include "lediv1.mm"
include "dividd.mm"
include "lemul2d.mm"
include "eqbrtrrd.mm"
include "adddird.mm"
include "eqtr4d.mm"
include "ltmul1dd.mm"
include "lelttrd.mm"
include "lttrd.mm"

theorem stoweidlem11
  let wph: wff ph
  let vt: setvar t
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem11.1: |- ( ph -> N e. NN )
  assume stoweidlem11.2: |- ( ph -> t e. T )
  assume stoweidlem11.3: |- ( ph -> j e. ( 1 ... N ) )
  assume stoweidlem11.4: |- ( ( ph /\ i e. ( 0 ... N ) ) -> ( X ` i ) : T --> RR )
  assume stoweidlem11.5: |- ( ( ph /\ i e. ( 0 ... N ) ) -> ( ( X ` i ) ` t ) <_ 1 )
  assume stoweidlem11.6: |- ( ( ph /\ i e. ( j ... N ) ) -> ( ( X ` i ) ` t ) < ( E / N ) )
  assume stoweidlem11.7: |- ( ph -> E e. RR+ )
  assume stoweidlem11.8: |- ( ph -> E < ( 1 / 3 ) )

  disjoint i j
  disjoint i t
  disjoint E i
  disjoint E t
  disjoint N i
  disjoint N t
  disjoint i ph
  disjoint T t
  disjoint X t
  disjoint k x
  assert |- ( ph -> ( ( t e. T |-> sum_ i e. ( 0 ... N ) ( E x. ( ( X ` i ) ` t ) ) ) ` t ) < ( ( j + ( 1 / 3 ) ) x. E ) )

  proof
    wph
    vt
    cv
    #
    vt
    cT
    cc0
    cN
    cfz
    co
    #
    cE
    @0
    vi
    cv
    #
    cX
    cfv
    #
    cfv
    #
    cmul
    co
    #
    vi
    csu
    #
    cmpt
    #
    cfv
    #
    @6
    vj
    cv
    #
    c1
    c3
    cdiv
    co
    #
    caddc
    co
    #
    cE
    cmul
    co
    #
    clt
    wph
    @0
    cT
    wcel
    #
    @6
    cvv
    wcel
    @8
    @6
    wceq
    stoweidlem11.2
    @1
    @5
    vi
    sumex
    vt
    cT
    @6
    cvv
    @7
    @7
    eqid
    fvmpt2
    sylancl
    wph
    @6
    cE
    @9
    cmul
    co
    #
    cN
    @9
    cmin
    co
    #
    c1
    caddc
    co
    #
    cE
    cE
    cN
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @12
    wph
    @1
    @5
    vi
    wph
    cc0
    cN
    fzfid
    #
    wph
    @2
    @1
    wcel
    #
    wa
    #
    cE
    @4
    wph
    cE
    cr
    wcel
    #
    @22
    wph
    cE
    stoweidlem11.7
    rpred
    #
    adantr
    @23
    cT
    cr
    @0
    @3
    stoweidlem11.4
    wph
    @13
    @22
    stoweidlem11.2
    adantr
    ffvelrnd
    #
    remulcld
    fsumrecl
    #
    wph
    @14
    @19
    wph
    cE
    @9
    @25
    wph
    @9
    wph
    c1
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    c1
    @9
    cle
    wbr
    #
    wph
    @9
    c1
    cuz
    cfv
    #
    wcel
    #
    @28
    @29
    @30
    w3a
    wph
    @9
    c1
    cN
    cfz
    co
    wcel
    #
    @32
    stoweidlem11.3
    @9
    c1
    cN
    elfzuz
    syl
    #
    c1
    @9
    eluz2
    sylib
    #
    simp2d
    #
    zred
    #
    remulcld
    #
    wph
    @16
    @18
    wph
    @15
    c1
    wph
    cN
    @9
    wph
    cN
    stoweidlem11.1
    nnred
    #
    @37
    resubcld
    wph
    1red
    #
    readdcld
    #
    wph
    cE
    @17
    @25
    wph
    cE
    cN
    @25
    stoweidlem11.1
    nndivred
    #
    remulcld
    remulcld
    #
    readdcld
    #
    wph
    @11
    cE
    wph
    @9
    @10
    @37
    wph
    c3
    c3
    cr
    wcel
    wph
    3re
    a1i
    c3
    cc0
    wne
    wph
    3ne0
    a1i
    rereccld
    #
    readdcld
    #
    @25
    remulcld
    #
    wph
    @6
    cc0
    @9
    c1
    cmin
    co
    #
    cfz
    co
    #
    @5
    vi
    csu
    #
    @19
    caddc
    co
    #
    @20
    @27
    wph
    @50
    @19
    wph
    @49
    @5
    vi
    wph
    cc0
    @48
    fzfid
    #
    wph
    @2
    @49
    wcel
    #
    wa
    #
    cE
    @4
    wph
    @24
    @53
    @25
    adantr
    #
    wph
    @53
    @22
    @4
    cr
    wcel
    #
    wph
    @49
    @1
    @2
    wph
    cN
    @48
    cuz
    cfv
    wcel
    #
    @49
    @1
    wss
    wph
    @48
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @48
    cN
    cle
    wbr
    @57
    wph
    @33
    @29
    @58
    stoweidlem11.3
    @9
    c1
    cN
    elfzelz
    @9
    peano2zm
    3syl
    wph
    cN
    stoweidlem11.1
    nnzd
    #
    wph
    @48
    @9
    cN
    wph
    @9
    c1
    @37
    @40
    resubcld
    @37
    @39
    wph
    @9
    @37
    lem1d
    wph
    @33
    cN
    @9
    cuz
    cfv
    wcel
    #
    @9
    cN
    cle
    wbr
    stoweidlem11.3
    @9
    c1
    cN
    elfzuz3
    #
    @9
    cN
    eluzle
    3syl
    letrd
    @48
    cN
    eluz2
    syl3anbrc
    @48
    cc0
    cN
    fzss2
    syl
    sselda
    #
    @26
    syldan
    #
    remulcld
    #
    fsumrecl
    #
    @43
    readdcld
    @44
    wph
    @6
    @50
    @9
    cN
    cfz
    co
    #
    @5
    vi
    csu
    #
    caddc
    co
    @51
    clt
    wph
    @49
    @67
    @5
    @1
    vi
    wph
    @48
    @9
    clt
    wbr
    @49
    @67
    cin
    c0
    wceq
    wph
    @9
    @37
    ltm1d
    cc0
    @48
    @9
    cN
    fzdisj
    syl
    wph
    @1
    @49
    @48
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cun
    #
    @49
    @67
    cun
    wph
    @48
    @1
    wcel
    @1
    @71
    wceq
    wph
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @1
    @48
    wph
    cc0
    @72
    c1
    caddc
    co
    #
    cfz
    co
    @73
    @1
    cc0
    @72
    fzssp1
    wph
    @74
    cN
    cc0
    cfz
    wph
    cN
    c1
    wph
    cN
    stoweidlem11.1
    nncnd
    #
    wph
    1cnd
    #
    npcand
    oveq2d
    syl5sseq
    wph
    @48
    c1
    c1
    cmin
    co
    #
    @72
    cfz
    co
    #
    @73
    wph
    @33
    @48
    @78
    wcel
    #
    stoweidlem11.3
    wph
    @28
    @59
    @29
    @28
    @33
    @79
    wb
    wph
    1zzd
    #
    @60
    @36
    @80
    @9
    c1
    c1
    cN
    fzsubel
    syl22anc
    mpbid
    @77
    cc0
    @72
    cfz
    1m1e0
    oveq1i
    syl6eleq
    sseldd
    @48
    cc0
    cN
    fzsplit
    syl
    wph
    @70
    @67
    @49
    wph
    @69
    @9
    cN
    cfz
    wph
    @9
    c1
    wph
    @9
    @36
    zcnd
    #
    @76
    npcand
    #
    oveq1d
    uneq2d
    eqtrd
    @21
    @23
    cE
    @4
    wph
    cE
    cc
    wcel
    #
    @22
    wph
    cE
    stoweidlem11.7
    rpcnd
    #
    adantr
    @23
    @4
    @26
    recnd
    mulcld
    fsumsplit
    wph
    @68
    @19
    @50
    wph
    @67
    @5
    vi
    wph
    @9
    cN
    fzfid
    #
    wph
    @2
    @67
    wcel
    #
    wa
    #
    cE
    @4
    wph
    @24
    @86
    @25
    adantr
    #
    @87
    cT
    cr
    @0
    @3
    wph
    @86
    @22
    cT
    cr
    @3
    wf
    wph
    @67
    @1
    @2
    wph
    @9
    cc0
    cuz
    cfv
    #
    wcel
    #
    @67
    @1
    wss
    wph
    cc0
    cz
    wcel
    #
    @29
    cc0
    @9
    cle
    wbr
    @90
    wph
    0zd
    @36
    wph
    cc0
    c1
    @9
    wph
    0red
    #
    @40
    @37
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    wph
    @28
    @29
    @30
    @35
    simp3d
    letrd
    cc0
    @9
    eluz2
    syl3anbrc
    @9
    cc0
    cN
    fzss1
    syl
    sselda
    stoweidlem11.4
    syldan
    wph
    @13
    @86
    stoweidlem11.2
    adantr
    ffvelrnd
    #
    remulcld
    #
    fsumrecl
    @43
    @66
    wph
    @68
    @67
    @18
    vi
    csu
    #
    @19
    clt
    wph
    @67
    @5
    @18
    vi
    @85
    wph
    @33
    @61
    cN
    @67
    wcel
    @67
    c0
    wne
    stoweidlem11.3
    @62
    @9
    cN
    eluzfz2
    @67
    cN
    ne0i
    4syl
    @94
    @87
    cE
    @17
    @88
    @87
    cE
    cN
    @88
    wph
    cN
    cn
    wcel
    @86
    stoweidlem11.1
    adantr
    nndivred
    #
    remulcld
    @87
    @4
    @17
    clt
    wbr
    #
    @5
    @18
    clt
    wbr
    #
    stoweidlem11.6
    @87
    @56
    @17
    cr
    wcel
    @24
    cc0
    cE
    clt
    wbr
    #
    @97
    @98
    wb
    @93
    @96
    @88
    wph
    @99
    @86
    wph
    cE
    stoweidlem11.7
    rpgt0d
    #
    adantr
    @4
    @17
    cE
    ltmul2
    syl112anc
    mpbid
    fsumlt
    wph
    @95
    @67
    chash
    cfv
    #
    @18
    cmul
    co
    #
    @19
    wph
    @67
    cfn
    wcel
    @18
    cc
    wcel
    @95
    @102
    wceq
    @85
    wph
    cE
    @17
    @84
    wph
    cE
    cN
    @84
    @75
    wph
    cN
    stoweidlem11.1
    nnne0d
    #
    divcld
    #
    mulcld
    @67
    @18
    vi
    fsumconst
    syl2anc
    wph
    @101
    @16
    @18
    cmul
    wph
    @33
    @61
    @101
    @16
    wceq
    stoweidlem11.3
    @62
    @9
    cN
    hashfz
    3syl
    oveq1d
    eqtrd
    breqtrd
    ltadd2dd
    eqbrtrd
    wph
    @50
    @14
    @19
    @66
    @38
    @43
    wph
    @50
    @49
    cE
    vi
    csu
    #
    @14
    cle
    wph
    @49
    @5
    cE
    vi
    @52
    @65
    @55
    @54
    @5
    cE
    c1
    cmul
    co
    #
    cE
    cle
    @54
    @4
    c1
    cle
    wbr
    #
    @5
    @106
    cle
    wbr
    #
    wph
    @53
    @22
    @107
    @63
    stoweidlem11.5
    syldan
    @54
    @56
    c1
    cr
    wcel
    @24
    @99
    @107
    @108
    wb
    @64
    @54
    1red
    @55
    wph
    @99
    @53
    @100
    adantr
    @4
    c1
    cE
    lemul2
    syl112anc
    mpbid
    wph
    @106
    cE
    wceq
    @53
    wph
    cE
    @84
    mulid1d
    #
    adantr
    breqtrd
    fsumle
    wph
    @105
    @49
    chash
    cfv
    #
    cE
    cmul
    co
    #
    @9
    cE
    cmul
    co
    #
    @14
    wph
    @49
    cfn
    wcel
    @83
    @105
    @111
    wceq
    @52
    @84
    @49
    cE
    vi
    fsumconst
    syl2anc
    wph
    @110
    @9
    cE
    cmul
    wph
    @110
    @48
    cc0
    cmin
    co
    #
    c1
    caddc
    co
    #
    @69
    @9
    wph
    @48
    @89
    wcel
    #
    @110
    @114
    wceq
    wph
    @91
    @9
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @115
    0z
    wph
    @9
    @31
    @117
    @34
    c1
    @116
    cuz
    1e0p1
    fveq2i
    syl6eleq
    cc0
    @9
    eluzp1m1
    sylancr
    cc0
    @48
    hashfz
    syl
    wph
    @113
    @48
    c1
    caddc
    wph
    @48
    wph
    @9
    c1
    @81
    @76
    subcld
    subid1d
    oveq1d
    @82
    3eqtrd
    oveq1d
    wph
    @9
    cE
    @81
    @84
    mulcomd
    3eqtrd
    breqtrd
    leadd1dd
    ltletrd
    wph
    @20
    @14
    cE
    cE
    cmul
    co
    #
    caddc
    co
    #
    @12
    @44
    wph
    @14
    @118
    @38
    wph
    cE
    cE
    @25
    @25
    remulcld
    #
    readdcld
    @47
    wph
    @14
    cE
    @16
    @17
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    @20
    @119
    cle
    wph
    @122
    @19
    @14
    caddc
    wph
    cE
    @16
    @17
    @84
    wph
    @15
    c1
    wph
    cN
    @9
    @75
    @81
    subcld
    #
    @76
    addcld
    #
    @104
    mul12d
    oveq2d
    wph
    @122
    @118
    @14
    wph
    cE
    @121
    @25
    wph
    @16
    @17
    @41
    @42
    remulcld
    #
    remulcld
    @120
    @38
    wph
    @121
    cE
    cle
    wbr
    @122
    @118
    cle
    wbr
    wph
    @121
    cE
    @16
    cN
    cdiv
    co
    #
    cmul
    co
    #
    cE
    cle
    wph
    @16
    cE
    cN
    @124
    @84
    @75
    @103
    div12d
    wph
    @127
    @106
    cE
    cle
    wph
    @126
    c1
    cle
    wbr
    @127
    @106
    cle
    wbr
    wph
    @126
    cN
    cN
    cdiv
    co
    #
    c1
    cle
    wph
    @16
    cN
    cle
    wbr
    #
    @126
    @128
    cle
    wbr
    #
    wph
    cN
    c1
    @9
    cmin
    co
    #
    caddc
    co
    #
    cN
    cc0
    caddc
    co
    @16
    cN
    cle
    wph
    @131
    cc0
    cN
    wph
    c1
    @9
    @40
    @37
    resubcld
    @92
    @39
    wph
    @131
    cc0
    cle
    wbr
    @30
    wph
    @33
    @30
    stoweidlem11.3
    @9
    c1
    cN
    elfzle1
    syl
    wph
    c1
    @9
    @40
    @37
    suble0d
    mpbird
    leadd2dd
    wph
    @132
    c1
    @15
    caddc
    co
    @16
    wph
    cN
    c1
    @9
    @75
    @76
    @81
    addsub12d
    wph
    c1
    @15
    @76
    @123
    addcomd
    eqtrd
    wph
    cN
    @75
    addid1d
    3brtr3d
    wph
    @16
    cr
    wcel
    cN
    cr
    wcel
    #
    @133
    cc0
    cN
    clt
    wbr
    @129
    @130
    wb
    @41
    @39
    @39
    wph
    cN
    stoweidlem11.1
    nngt0d
    @16
    cN
    cN
    lediv1
    syl112anc
    mpbid
    wph
    cN
    @75
    @103
    dividd
    breqtrd
    wph
    @126
    c1
    cE
    wph
    @16
    cN
    @41
    stoweidlem11.1
    nndivred
    @40
    stoweidlem11.7
    lemul2d
    mpbid
    @109
    breqtrd
    eqbrtrd
    wph
    @121
    cE
    cE
    @125
    @25
    stoweidlem11.7
    lemul2d
    mpbid
    leadd2dd
    eqbrtrrd
    wph
    @119
    @9
    cE
    caddc
    co
    #
    cE
    cmul
    co
    #
    @12
    clt
    wph
    @119
    @112
    @118
    caddc
    co
    @135
    wph
    @14
    @112
    @118
    caddc
    wph
    cE
    @9
    @84
    @81
    mulcomd
    oveq1d
    wph
    @9
    cE
    cE
    @81
    @84
    @84
    adddird
    eqtr4d
    wph
    @134
    @11
    cE
    wph
    @9
    cE
    @37
    @25
    readdcld
    @46
    stoweidlem11.7
    wph
    cE
    @10
    @9
    @25
    @45
    @37
    stoweidlem11.8
    ltadd2dd
    ltmul1dd
    eqbrtrd
    lelttrd
    lttrd
    eqbrtrd
end
