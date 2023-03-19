include "cdm.mm"
include "wf1.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "crn.mm"
include "cmin.mm"
include "w3a.mm"
include "wi.mm"
include "wfn.mm"
include "f1fn.mm"
include "dffn3.mm"
include "sylib.mm"
include "cn0.mm"
include "lencl.mm"
include "ffn.mm"
include "fnfz0hash.mm"
include "syl2an.mm"
include "ffz0iswrd.mm"
include "lsw.mm"
include "ad6antr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ad4antlr.mm"
include "eqcom.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "adantld.mm"
include "imp.mm"
include "3eqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "cz.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "nn0re.mm"
include "lem1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "ssralv.mm"
include "3syl.mm"
include "simpr.mm"
include "adantr.mm"
include "wrdf.mm"
include "simpll.mm"
include "fzossrbm1.mm"
include "adantl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "exp31.mm"
include "ad3antrrr.mm"
include "biimpi.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "ralimdva.mm"
include "syldc.mm"
include "impcom.mm"
include "cn.mm"
include "wb.mm"
include "breq2.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "1red.mm"
include "lesubaddd.mm"
include "2m1e1.mm"
include "breq1i.mm"
include "elnnnn0c.mm"
include "simplbi2.mm"
include "sylbird.mm"
include "sylbid.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "fzoend.mm"
include "fveq2.mm"
include "preq12d.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "npcand.mm"
include "preq2d.mm"
include "eqeq2d.mm"
include "com12.mm"
include "syl6bi.mm"
include "com3r.mm"
include "imp31.mm"
include "preq2.mm"
include "mpbird.mm"
include "3jca.mm"
include "exp41.mm"
include "com13.mm"
include "mpcom.mm"
include "mpd.mm"
include "expcom.mm"
include "com14.mm"
include "sylan.mm"
include "3imp.mm"

theorem clwlkclwwlklem2
  let cP: class P
  let cR: class R
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cV: class V
  let vf: setvar f
  let vx: setvar x

  disjoint E i
  disjoint P i
  disjoint R i
  disjoint V i
  disjoint F i
  disjoint E f
  disjoint E x
  disjoint f i
  disjoint f x
  disjoint i x
  disjoint P f
  disjoint P x
  disjoint R f
  disjoint R x
  disjoint V f
  disjoint V x
  assert |- ( ( ( E : dom E -1-1-> R /\ F e. Word dom E ) /\ ( P : ( 0 ... ( # ` F ) ) --> V /\ 2 <_ ( # ` P ) ) /\ ( A. i e. ( 0 ..^ ( # ` F ) ) ( E ` ( F ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) ) -> ( ( lastS ` P ) = ( P ` 0 ) /\ A. i e. ( 0 ..^ ( ( # ` F ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E /\ { ( P ` ( ( # ` F ) - 1 ) ) , ( P ` 0 ) } e. ran E ) )

  proof
    cE
    cdm
    #
    cR
    cE
    wf1
    #
    cF
    @0
    cword
    wcel
    #
    wa
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
    wf
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vi
    cv
    #
    cF
    cfv
    #
    cE
    cfv
    #
    @9
    cP
    cfv
    #
    @9
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
    vi
    cc0
    @3
    cfzo
    co
    #
    wral
    #
    cc0
    cP
    cfv
    #
    @3
    cP
    cfv
    #
    wceq
    #
    wa
    #
    cP
    clsw
    cfv
    #
    @19
    wceq
    #
    @15
    cE
    crn
    #
    wcel
    #
    vi
    cc0
    @3
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @27
    cP
    cfv
    #
    @19
    cpr
    #
    @25
    wcel
    #
    w3a
    #
    @1
    @0
    @25
    cE
    wf
    #
    @2
    @8
    @22
    @33
    wi
    #
    wi
    @1
    cE
    @0
    wfn
    @34
    @0
    cR
    cE
    f1fn
    @0
    cE
    dffn3
    sylib
    @8
    @34
    @2
    wa
    #
    @35
    @5
    @7
    @36
    @35
    wi
    @36
    @7
    @5
    @35
    @34
    @2
    @7
    @5
    @35
    wi
    wi
    @5
    @2
    @7
    @34
    @35
    @2
    @5
    @7
    @34
    @35
    wi
    wi
    #
    @2
    @5
    wa
    @6
    @3
    c1
    caddc
    co
    #
    wceq
    #
    @37
    @2
    @3
    cn0
    wcel
    #
    cP
    @4
    wfn
    @39
    @5
    @0
    cF
    lencl
    #
    @4
    cV
    cP
    ffn
    cP
    @3
    fnfz0hash
    syl2an
    @2
    @5
    @39
    @37
    wi
    #
    @40
    @2
    @5
    @42
    wi
    @41
    @5
    @2
    @40
    @42
    @5
    cP
    cV
    cword
    #
    wcel
    #
    @2
    @40
    @42
    wi
    wi
    cV
    @3
    cP
    ffz0iswrd
    @44
    @2
    @40
    @39
    @37
    @44
    @2
    wa
    #
    @40
    wa
    #
    @39
    wa
    #
    @7
    @34
    @22
    @33
    @47
    @7
    wa
    #
    @34
    wa
    #
    @22
    wa
    #
    @24
    @29
    @32
    @50
    @23
    @6
    c1
    cmin
    co
    #
    cP
    cfv
    #
    @38
    c1
    cmin
    co
    #
    cP
    cfv
    #
    @19
    @44
    @23
    @52
    wceq
    @2
    @40
    @39
    @7
    @34
    @22
    cP
    @43
    lsw
    ad6antr
    @39
    @52
    @54
    wceq
    @46
    @7
    @34
    @22
    @39
    @51
    @53
    cP
    @6
    @38
    c1
    cmin
    oveq1
    fveq2d
    ad4antlr
    @49
    @22
    @54
    @19
    wceq
    #
    @49
    @21
    @55
    @18
    @21
    @20
    @19
    wceq
    #
    @49
    @55
    @19
    @20
    eqcom
    @49
    @56
    @55
    @49
    @20
    @54
    @19
    @49
    @3
    @53
    cP
    @40
    @3
    @53
    wceq
    @45
    @39
    @7
    @34
    @40
    @53
    @3
    @40
    @3
    c1
    @3
    nn0cn
    #
    @40
    1cnd
    #
    pncand
    eqcomd
    ad4antlr
    fveq2d
    eqeq1d
    biimpd
    syl5bi
    adantld
    imp
    3eqtrd
    @22
    @49
    @29
    @18
    @49
    @29
    wi
    @21
    @49
    @18
    @16
    vi
    @28
    wral
    #
    @29
    @49
    @3
    @27
    cuz
    cfv
    wcel
    #
    @28
    @17
    wss
    #
    @18
    @59
    wi
    @40
    @60
    @45
    @39
    @7
    @34
    @40
    @27
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @27
    @3
    cle
    wbr
    @60
    @40
    @63
    @62
    @3
    nn0z
    #
    @3
    peano2zm
    syl
    @64
    @40
    @3
    @3
    nn0re
    #
    lem1d
    @27
    @3
    eluz2
    syl3anbrc
    ad4antlr
    @27
    cc0
    @3
    fzoss2
    @16
    vi
    @28
    @17
    ssralv
    3syl
    @49
    @16
    @26
    vi
    @28
    @49
    @9
    @28
    wcel
    #
    wa
    #
    @26
    @16
    @11
    @25
    wcel
    @67
    @0
    @25
    @10
    cE
    @49
    @34
    @66
    @48
    @34
    simpr
    #
    adantr
    @49
    @66
    @10
    @0
    wcel
    #
    @46
    @66
    @69
    wi
    #
    @39
    @7
    @34
    @45
    @40
    @70
    @2
    @40
    @70
    wi
    #
    @44
    @2
    @17
    @0
    cF
    wf
    #
    @71
    @0
    cF
    wrdf
    #
    @72
    @40
    @66
    @69
    @72
    @40
    wa
    #
    @66
    wa
    @17
    @0
    @9
    cF
    @72
    @40
    @66
    simpll
    @74
    @28
    @17
    @9
    @40
    @61
    @72
    @40
    @63
    @61
    @64
    @3
    fzossrbm1
    syl
    adantl
    sselda
    ffvelrnd
    exp31
    syl
    adantl
    imp
    ad3antrrr
    imp
    ffvelrnd
    @16
    @15
    @11
    @25
    @16
    @15
    @11
    wceq
    @11
    @15
    eqcom
    biimpi
    eleq1d
    syl5ibrcom
    ralimdva
    syldc
    adantr
    impcom
    @50
    @32
    @30
    @20
    cpr
    #
    @25
    wcel
    #
    @22
    @49
    @76
    @18
    @49
    @76
    wi
    @21
    @49
    @18
    @27
    cF
    cfv
    #
    cE
    cfv
    #
    @30
    @27
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
    @76
    @49
    @16
    @82
    vi
    @27
    @17
    @49
    cc0
    @17
    wcel
    #
    @27
    @17
    wcel
    #
    @49
    @3
    cn
    wcel
    #
    @83
    @48
    @85
    @34
    @47
    @7
    @85
    @47
    @7
    c2
    @38
    cle
    wbr
    #
    @85
    @39
    @7
    @86
    wb
    @46
    @6
    @38
    c2
    cle
    breq2
    #
    adantl
    @46
    @86
    @85
    wi
    #
    @39
    @40
    @88
    @45
    @40
    @86
    c2
    c1
    cmin
    co
    #
    @3
    cle
    wbr
    #
    @85
    @40
    c2
    c1
    @3
    c2
    cr
    wcel
    @40
    2re
    a1i
    @40
    1red
    @65
    lesubaddd
    @90
    c1
    @3
    cle
    wbr
    #
    @40
    @85
    @89
    c1
    @3
    cle
    2m1e1
    breq1i
    @85
    @40
    @91
    @3
    elnnnn0c
    simplbi2
    syl5bi
    sylbird
    #
    adantl
    adantr
    sylbid
    imp
    adantr
    @3
    lbfzo0
    #
    sylibr
    cc0
    @3
    fzoend
    #
    syl
    @9
    @27
    wceq
    #
    @16
    @82
    wb
    @49
    @95
    @11
    @78
    @15
    @81
    @95
    @10
    @77
    cE
    @9
    @27
    cF
    fveq2
    fveq2d
    @95
    @12
    @30
    @14
    @80
    @9
    @27
    cP
    fveq2
    @95
    @13
    @79
    cP
    @9
    @27
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eqeq12d
    adantl
    rspcdv
    @49
    @82
    @78
    @75
    wceq
    #
    @76
    @49
    @81
    @75
    @78
    @49
    @80
    @20
    @30
    @49
    @79
    @3
    cP
    @40
    @79
    @3
    wceq
    @45
    @39
    @7
    @34
    @40
    @3
    c1
    @57
    @58
    npcand
    ad4antlr
    fveq2d
    preq2d
    eqeq2d
    @49
    @76
    @96
    @78
    @25
    wcel
    @49
    @0
    @25
    @77
    cE
    @68
    @48
    @77
    @0
    wcel
    @34
    @48
    @17
    @0
    @27
    cF
    @2
    @72
    @44
    @40
    @39
    @7
    @73
    ad4antlr
    @48
    @83
    @84
    @48
    @85
    @83
    @46
    @39
    @7
    @85
    @40
    @39
    @7
    @85
    wi
    wi
    @45
    @39
    @7
    @40
    @85
    @39
    @7
    @86
    @40
    @85
    wi
    @87
    @40
    @86
    @85
    @92
    com12
    syl6bi
    com3r
    adantl
    imp31
    @93
    sylibr
    @94
    syl
    ffvelrnd
    adantr
    ffvelrnd
    @96
    @75
    @78
    @25
    @96
    @75
    @78
    wceq
    @78
    @75
    eqcom
    biimpi
    eleq1d
    syl5ibrcom
    sylbid
    syldc
    adantr
    impcom
    @22
    @32
    @76
    wb
    #
    @49
    @21
    @97
    @18
    @21
    @31
    @75
    @25
    @19
    @20
    @30
    preq2
    eleq1d
    adantl
    adantl
    mpbird
    3jca
    exp41
    exp41
    syl
    com13
    mpcom
    imp
    mpd
    expcom
    com14
    imp
    com13
    imp
    com12
    sylan
    3imp
end
