include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wf1.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "ccnv.mm"
include "wfun.mm"
include "wi.mm"
include "cfn.mm"
include "wf.mm"
include "wrdfin.mm"
include "wrdf.mm"
include "wa.mm"
include "weq.mm"
include "simpr.mm"
include "adantr.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "preq12d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "anim12ii.mm"
include "simpl.mm"
include "eqcomd.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "wo.mm"
include "fvex.mm"
include "preq12b.mm"
include "dff13.mm"
include "elfzofz.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "syl2an.mm"
include "a1dd.mm"
include "com14.mm"
include "cn0.mm"
include "hashcl.mm"
include "a1i.mm"
include "fzofzp1.mm"
include "anim12d1.mm"
include "imp.mm"
include "syl.mm"
include "anim12d.mm"
include "expimpd.mm"
include "wb.mm"
include "elfzonn0.mm"
include "c2.mm"
include "cc.mm"
include "nn0cn.mm"
include "add1p1.mm"
include "wne.mm"
include "2cnd.mm"
include "2ne0.mm"
include "addn0nid.mm"
include "syl3anc.mm"
include "eqneqall.mm"
include "syl5com.mm"
include "sylbid.mm"
include "syld.mm"
include "ex.mm"
include "com3l.mm"
include "expd.mm"
include "com34.mm"
include "jaoi.mm"
include "adantld.mm"
include "syl5bi.mm"
include "com23.mm"
include "sylbi.mm"
include "com15.mm"
include "impcom.mm"
include "ralrimivv.mm"
include "adantlr.mm"
include "sylanbrc.mm"
include "df-f1.mm"
include "sylib.mm"
include "syl2anc.mm"

theorem upgrwlkdvdelem
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y

  disjoint F k
  disjoint I k
  disjoint P k
  disjoint F a
  disjoint F b
  disjoint F x
  disjoint F y
  disjoint a b
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint P a
  disjoint P b
  disjoint P x
  disjoint P y
  disjoint V x
  disjoint V y
  assert |- ( ( P : ( 0 ... ( # ` F ) ) -1-1-> V /\ F e. Word dom I ) -> ( A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } -> Fun `' F ) )

  proof
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf1
    #
    vk
    cv
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @5
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    vk
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    cF
    ccnv
    wfun
    #
    wi
    #
    @1
    cF
    cfn
    wcel
    #
    @13
    @0
    cF
    wf
    #
    @4
    @16
    wi
    @0
    cF
    wrdfin
    @0
    cF
    wrdf
    @17
    @18
    wa
    #
    @4
    @14
    @15
    @19
    @4
    @14
    wa
    #
    @15
    @19
    @20
    wa
    #
    @18
    @15
    wa
    #
    @15
    @21
    @13
    @0
    cF
    wf1
    #
    @22
    @21
    @18
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @13
    wral
    vx
    @13
    wral
    #
    @23
    @19
    @18
    @20
    @17
    @18
    simpr
    adantr
    @17
    @20
    @31
    @18
    @17
    @20
    wa
    @30
    vx
    vy
    @13
    @13
    @20
    @17
    @24
    @13
    wcel
    #
    @26
    @13
    wcel
    #
    wa
    #
    @30
    wi
    #
    @4
    @14
    @17
    @35
    wi
    @34
    @14
    @17
    @4
    @30
    @34
    @14
    @25
    cI
    cfv
    #
    @24
    cP
    cfv
    #
    @24
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    @27
    cI
    cfv
    #
    @26
    cP
    cfv
    #
    @26
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    wa
    #
    @17
    @4
    @30
    wi
    wi
    @32
    @14
    @41
    @33
    @47
    @12
    @41
    vk
    @24
    @13
    vk
    vx
    weq
    #
    @7
    @36
    @11
    @40
    @49
    @6
    @25
    cI
    @5
    @24
    cF
    fveq2
    fveq2d
    @49
    @8
    @37
    @10
    @39
    @5
    @24
    cP
    fveq2
    @49
    @9
    @38
    cP
    @5
    @24
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eqeq12d
    rspcv
    @12
    @47
    vk
    @26
    @13
    vk
    vy
    weq
    #
    @7
    @42
    @11
    @46
    @50
    @6
    @27
    cI
    @5
    @26
    cF
    fveq2
    fveq2d
    @50
    @8
    @43
    @10
    @45
    @5
    @26
    cP
    fveq2
    @50
    @9
    @44
    cP
    @5
    @26
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eqeq12d
    rspcv
    anim12ii
    @28
    @48
    @17
    @4
    @34
    @29
    @28
    @36
    @42
    wceq
    #
    @48
    @17
    @4
    @34
    @29
    wi
    #
    wi
    wi
    #
    wi
    @25
    @27
    cI
    fveq2
    @51
    @48
    @53
    @51
    @48
    wa
    #
    @40
    @46
    wceq
    #
    @53
    @54
    @40
    @36
    @42
    @46
    @48
    @40
    @36
    wceq
    @51
    @48
    @36
    @40
    @41
    @47
    simpl
    eqcomd
    adantl
    @51
    @48
    simpl
    @48
    @47
    @51
    @41
    @47
    simpr
    adantl
    3eqtrd
    @55
    @37
    @43
    wceq
    #
    @39
    @45
    wceq
    #
    wa
    #
    @37
    @45
    wceq
    #
    @39
    @43
    wceq
    #
    wa
    #
    wo
    #
    @53
    @37
    @39
    @43
    @45
    @24
    cP
    fvex
    @38
    cP
    fvex
    @26
    cP
    fvex
    @44
    cP
    fvex
    preq12b
    @62
    @4
    @17
    @52
    @4
    @3
    cV
    cP
    wf
    #
    va
    cv
    #
    cP
    cfv
    #
    vb
    cv
    #
    cP
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    @3
    wral
    va
    @3
    wral
    #
    wa
    @62
    @17
    @52
    wi
    #
    va
    vb
    @3
    cV
    cP
    dff13
    @62
    @71
    @72
    @63
    @58
    @71
    @72
    wi
    #
    @61
    @56
    @73
    @57
    @34
    @71
    @17
    @56
    @29
    @34
    @71
    @56
    @29
    wi
    #
    @17
    @32
    @24
    @3
    wcel
    #
    @26
    @3
    wcel
    #
    @71
    @74
    wi
    @33
    @24
    cc0
    @2
    elfzofz
    #
    @26
    cc0
    @2
    elfzofz
    #
    @70
    @74
    @37
    @67
    wceq
    #
    vx
    vb
    weq
    #
    wi
    #
    va
    vb
    @24
    @26
    @3
    @3
    va
    vx
    weq
    #
    @68
    @79
    @69
    @80
    @82
    @65
    @37
    @67
    @64
    @24
    cP
    fveq2
    eqeq1d
    @64
    @24
    @66
    eqeq1
    imbi12d
    #
    vb
    vy
    weq
    #
    @79
    @56
    @80
    @29
    @84
    @67
    @43
    @37
    @66
    @26
    cP
    fveq2
    #
    eqeq2d
    @66
    @26
    @24
    eqeq2
    imbi12d
    rspc2v
    syl2an
    a1dd
    com14
    adantr
    @34
    @71
    @17
    @61
    @29
    @34
    @71
    @61
    @17
    @29
    @34
    @71
    @61
    @17
    @29
    wi
    @17
    @34
    @71
    @61
    wa
    #
    @29
    @17
    @2
    cn0
    wcel
    #
    @34
    @86
    @29
    wi
    #
    wi
    cF
    hashcl
    @87
    @34
    @88
    @87
    @34
    wa
    #
    @86
    @24
    @44
    wceq
    #
    @38
    @26
    wceq
    #
    wa
    #
    @29
    @89
    @71
    @61
    @92
    @89
    @71
    wa
    @59
    @90
    @60
    @91
    @89
    @71
    @59
    @90
    wi
    #
    @89
    @75
    @44
    @3
    wcel
    #
    wa
    #
    @71
    @93
    wi
    @87
    @34
    @95
    @87
    @32
    @75
    @33
    @94
    @32
    @75
    wi
    @87
    @77
    a1i
    cc0
    @2
    @26
    fzofzp1
    anim12d1
    imp
    @70
    @93
    @81
    va
    vb
    @24
    @44
    @3
    @3
    @83
    @66
    @44
    wceq
    #
    @79
    @59
    @80
    @90
    @96
    @67
    @45
    @37
    @66
    @44
    cP
    fveq2
    eqeq2d
    @66
    @44
    @24
    eqeq2
    imbi12d
    rspc2v
    syl
    imp
    @89
    @71
    @60
    @91
    wi
    #
    @89
    @38
    @3
    wcel
    #
    @76
    wa
    #
    @71
    @97
    wi
    @87
    @34
    @99
    @87
    @32
    @98
    @33
    @76
    @32
    @98
    wi
    @87
    cc0
    @2
    @24
    fzofzp1
    a1i
    @78
    anim12d1
    imp
    @70
    @97
    @39
    @67
    wceq
    #
    @38
    @66
    wceq
    #
    wi
    va
    vb
    @38
    @26
    @3
    @3
    @64
    @38
    wceq
    #
    @68
    @100
    @69
    @101
    @102
    @65
    @39
    @67
    @64
    @38
    cP
    fveq2
    eqeq1d
    @64
    @38
    @66
    eqeq1
    imbi12d
    @84
    @100
    @60
    @101
    @91
    @84
    @67
    @43
    @39
    @85
    eqeq2d
    @66
    @26
    @38
    eqeq2
    imbi12d
    rspc2v
    syl
    imp
    anim12d
    expimpd
    @34
    @92
    @29
    wi
    @87
    @34
    @90
    @91
    @29
    @34
    @90
    wa
    @91
    @44
    c1
    caddc
    co
    #
    @26
    wceq
    #
    @29
    @90
    @91
    @104
    wb
    @34
    @90
    @38
    @103
    @26
    @24
    @44
    c1
    caddc
    oveq1
    eqeq1d
    adantl
    @34
    @104
    @29
    wi
    #
    @90
    @33
    @105
    @32
    @33
    @26
    cn0
    wcel
    #
    @105
    @26
    @2
    elfzonn0
    @106
    @104
    @26
    c2
    caddc
    co
    #
    @26
    wceq
    #
    @29
    @106
    @103
    @107
    @26
    @106
    @26
    cc
    wcel
    #
    @103
    @107
    wceq
    @26
    nn0cn
    #
    @26
    add1p1
    syl
    eqeq1d
    @106
    @107
    @26
    wne
    #
    @108
    @29
    @106
    @109
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    @111
    @110
    @106
    2cnd
    @112
    @106
    2ne0
    a1i
    @26
    c2
    addn0nid
    syl3anc
    @29
    @107
    @26
    eqneqall
    syl5com
    sylbid
    syl
    adantl
    adantr
    sylbid
    expimpd
    adantl
    syld
    ex
    syl
    com3l
    expd
    com34
    com14
    jaoi
    adantld
    syl5bi
    com23
    sylbi
    syl
    ex
    syl
    com15
    syld
    com14
    imp
    impcom
    ralrimivv
    adantlr
    vx
    vy
    @13
    @0
    cF
    dff13
    sylanbrc
    @13
    @0
    cF
    df-f1
    sylib
    @18
    @15
    simpr
    syl
    ex
    expd
    syl2anc
    impcom
end
