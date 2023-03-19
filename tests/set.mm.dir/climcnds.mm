include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "wa.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wf.mm"
include "cv.mm"
include "cn0.mm"
include "cfv.mm"
include "nnnn0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "2nn.mm"
include "simpr.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnred.mm"
include "wral.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "serfre.mm"
include "cle.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "cfz.mm"
include "simpl.mm"
include "elfznn.mm"
include "syl2an.mm"
include "simpll.mm"
include "elfz1eq.mm"
include "peano2nn0.mm"
include "syl.mm"
include "ad2antlr.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "breq2d.mm"
include "mulge0d.mm"
include "breqtrrd.mm"
include "syl2anc.mm"
include "sermono.mm"
include "adantlr.mm"
include "csu.mm"
include "wrex.mm"
include "2re.mm"
include "eqidd.mm"
include "isumrecl.mm"
include "remulcl.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "climcndslem2.mm"
include "cc.mm"
include "recnd.mm"
include "fsumser.mm"
include "fzfid.mm"
include "wss.mm"
include "ssriv.mm"
include "a1i.mm"
include "sylan.mm"
include "simplr.mm"
include "isumless.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "2pos.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "letrd.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "climsup.mm"
include "climrel.mm"
include "releldmi.mm"
include "nn0uz.mm"
include "1nn0.mm"
include "iserex.mm"
include "biimpar.mm"
include "syldan.mm"
include "peano2nn.mm"
include "eleq1.mm"
include "biimparc.mm"
include "0zd.mm"
include "ffvelrn.mm"
include "cmin.mm"
include "nn0red.mm"
include "2z.mm"
include "ax-mp.mm"
include "bernneq3.mm"
include "ltled.mm"
include "peano2zd.mm"
include "nnzd.mm"
include "eluz.mm"
include "mpbird.mm"
include "eluzp1m1.mm"
include "eluznn.mm"
include "elfzuz.mm"
include "climcndslem1.mm"
include "elfznn0.mm"
include "impbida.mm"

theorem climcnds
  let wph: wff ph
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vx: setvar x
  let cN: class N
  assume climcnds.1: |- ( ( ph /\ k e. NN ) -> ( F ` k ) e. RR )
  assume climcnds.2: |- ( ( ph /\ k e. NN ) -> 0 <_ ( F ` k ) )
  assume climcnds.3: |- ( ( ph /\ k e. NN ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )
  assume climcnds.4: |- ( ( ph /\ n e. NN0 ) -> ( G ` n ) = ( ( 2 ^ n ) x. ( F ` ( 2 ^ n ) ) ) )

  disjoint k n
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint G n
  disjoint k ph
  disjoint n ph
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint n x
  disjoint F x
  disjoint G j
  disjoint G x
  disjoint N x
  disjoint j ph
  disjoint ph x
  assert |- ( ph -> ( seq 1 ( + , F ) e. dom ~~> <-> seq 0 ( + , G ) e. dom ~~> ) )

  proof
    wph
    caddc
    cF
    c1
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    caddc
    cG
    cc0
    cseq
    #
    @1
    wcel
    #
    wph
    @2
    caddc
    cG
    c1
    cseq
    #
    @1
    wcel
    #
    @4
    wph
    @2
    wa
    #
    @5
    @5
    crn
    cr
    clt
    csup
    #
    cli
    wbr
    @6
    @7
    vx
    vj
    @5
    c1
    cn
    nnuz
    @7
    1zzd
    #
    wph
    cn
    cr
    @5
    wf
    @2
    wph
    vn
    cG
    c1
    cn
    nnuz
    wph
    1zzd
    #
    vn
    cv
    #
    cn
    wcel
    #
    wph
    @11
    cn0
    wcel
    #
    @11
    cG
    cfv
    #
    cr
    wcel
    #
    @11
    nnnn0
    wph
    @13
    wa
    #
    @14
    c2
    @11
    cexp
    co
    #
    @17
    cF
    cfv
    #
    cmul
    co
    #
    cr
    climcnds.4
    @16
    @17
    @18
    @16
    @17
    @16
    c2
    cn
    wcel
    #
    @13
    @17
    cn
    wcel
    #
    2nn
    wph
    @13
    simpr
    c2
    @11
    nnexpcl
    sylancr
    #
    nnred
    #
    @16
    @21
    vk
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    vk
    cn
    wral
    #
    @18
    cr
    wcel
    #
    @22
    wph
    @27
    @13
    wph
    @26
    vk
    cn
    climcnds.1
    ralrimiva
    adantr
    @26
    @28
    vk
    @17
    cn
    @24
    @17
    wceq
    #
    @25
    @18
    cr
    @24
    @17
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    #
    remulcld
    eqeltrd
    #
    sylan2
    #
    serfre
    adantr
    #
    wph
    vj
    cv
    #
    cn
    wcel
    #
    @35
    @5
    cfv
    #
    @35
    c1
    caddc
    co
    #
    @5
    cfv
    cle
    wbr
    @2
    wph
    @36
    wa
    #
    vn
    cG
    @35
    c1
    @38
    @39
    @35
    cn
    c1
    cuz
    cfv
    #
    wph
    @36
    simpr
    nnuz
    syl6eleq
    #
    @39
    @35
    cz
    wcel
    #
    @35
    @35
    cuz
    cfv
    #
    wcel
    @38
    @43
    wcel
    @36
    @42
    wph
    @35
    nnz
    #
    adantl
    @35
    uzid
    @35
    @35
    peano2uz
    3syl
    #
    @39
    wph
    @12
    @15
    @11
    c1
    @38
    cfz
    co
    #
    wcel
    wph
    @36
    simpl
    #
    @11
    @38
    elfznn
    @33
    syl2an
    @39
    @11
    @38
    @38
    cfz
    co
    #
    wcel
    #
    wa
    #
    wph
    @13
    cc0
    @14
    cle
    wbr
    #
    wph
    @36
    @49
    simpll
    @50
    @11
    @38
    cn0
    @49
    @11
    @38
    wceq
    @39
    @11
    @38
    elfz1eq
    adantl
    @36
    @38
    cn0
    wcel
    #
    wph
    @49
    @36
    @35
    cn0
    wcel
    #
    @52
    @35
    nnnn0
    #
    @35
    peano2nn0
    syl
    #
    ad2antlr
    eqeltrd
    @16
    cc0
    @19
    @14
    cle
    @16
    @17
    @18
    @23
    @31
    @16
    @17
    @16
    @17
    @22
    nnnn0d
    nn0ge0d
    @16
    @21
    cc0
    @25
    cle
    wbr
    #
    vk
    cn
    wral
    #
    cc0
    @18
    cle
    wbr
    #
    @22
    wph
    @57
    @13
    wph
    @56
    vk
    cn
    climcnds.2
    ralrimiva
    adantr
    @56
    @58
    vk
    @17
    cn
    @29
    @25
    @18
    cc0
    cle
    @30
    breq2d
    rspcv
    sylc
    mulge0d
    climcnds.4
    breqtrrd
    #
    syl2anc
    sermono
    adantlr
    @7
    c2
    cn
    @25
    vk
    csu
    #
    cmul
    co
    #
    cr
    wcel
    #
    @37
    @61
    cle
    wbr
    #
    vj
    cn
    wral
    #
    @37
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cn
    wral
    #
    vx
    cr
    wrex
    @7
    c2
    cr
    wcel
    #
    @60
    cr
    wcel
    #
    @62
    2re
    @7
    @25
    vk
    cF
    c1
    cn
    nnuz
    @9
    @7
    @24
    cn
    wcel
    #
    wa
    @25
    eqidd
    wph
    @70
    @26
    @2
    climcnds.1
    adantlr
    #
    wph
    @2
    simpr
    isumrecl
    #
    c2
    @60
    remulcl
    sylancr
    #
    @7
    @63
    vj
    cn
    @7
    @36
    wa
    #
    @37
    c2
    c2
    @35
    cexp
    co
    #
    @0
    cfv
    #
    cmul
    co
    #
    @61
    @7
    cn
    cr
    @35
    @5
    @34
    ffvelrnda
    @74
    @68
    @76
    cr
    wcel
    #
    @77
    cr
    wcel
    2re
    @74
    cn
    cr
    @75
    @0
    wph
    cn
    cr
    @0
    wf
    #
    @2
    @36
    wph
    vk
    cF
    c1
    cn
    nnuz
    @10
    climcnds.1
    serfre
    #
    ad2antrr
    @74
    @20
    @53
    @75
    cn
    wcel
    2nn
    @36
    @53
    @7
    @54
    adantl
    c2
    @35
    nnexpcl
    sylancr
    #
    ffvelrnd
    #
    c2
    @76
    remulcl
    sylancr
    @7
    @62
    @36
    @73
    adantr
    wph
    @36
    @37
    @77
    cle
    wbr
    @2
    wph
    vk
    vn
    cF
    cG
    @35
    climcnds.1
    climcnds.2
    climcnds.3
    climcnds.4
    climcndslem2
    adantlr
    @74
    @76
    @60
    cle
    wbr
    #
    @77
    @61
    cle
    wbr
    #
    @74
    c1
    @75
    cfz
    co
    #
    @25
    vk
    csu
    @76
    @60
    cle
    @74
    @25
    vk
    cF
    c1
    @75
    @74
    @24
    @85
    wcel
    #
    wa
    @25
    eqidd
    @74
    @75
    cn
    @40
    @81
    nnuz
    syl6eleq
    @74
    wph
    @70
    @25
    cc
    wcel
    @86
    wph
    @2
    @36
    simpll
    #
    @24
    @75
    elfznn
    #
    wph
    @70
    wa
    @25
    climcnds.1
    recnd
    syl2an
    fsumser
    @74
    @85
    @25
    vk
    cF
    c1
    cn
    nnuz
    @74
    1zzd
    @74
    c1
    @75
    fzfid
    @85
    cn
    wss
    @74
    vk
    @85
    cn
    @88
    ssriv
    a1i
    @74
    @70
    wa
    @25
    eqidd
    @7
    @70
    @26
    @36
    @71
    adantlr
    @74
    wph
    @70
    @56
    @87
    climcnds.2
    sylan
    wph
    @2
    @36
    simplr
    isumless
    eqbrtrrd
    @74
    @78
    @69
    @68
    cc0
    c2
    clt
    wbr
    #
    @83
    @84
    wb
    @82
    @7
    @69
    @36
    @72
    adantr
    @68
    @74
    2re
    a1i
    @89
    @74
    2pos
    a1i
    @76
    @60
    c2
    lemul2
    syl112anc
    mpbid
    letrd
    ralrimiva
    @67
    @64
    vx
    @61
    cr
    @65
    @61
    wceq
    @66
    @63
    vj
    cn
    @65
    @61
    @37
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    climsup
    @5
    @8
    cli
    climrel
    releldmi
    syl
    wph
    @4
    @6
    wph
    vn
    cG
    cc0
    c1
    cn0
    nn0uz
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    @16
    @14
    @32
    recnd
    #
    iserex
    biimpar
    syldan
    wph
    @4
    wa
    #
    @0
    @0
    crn
    cr
    clt
    csup
    #
    cli
    wbr
    @2
    @91
    vx
    vj
    @0
    c1
    cn
    nnuz
    @91
    1zzd
    wph
    @79
    @4
    @80
    adantr
    #
    wph
    @36
    @35
    @0
    cfv
    #
    @38
    @0
    cfv
    cle
    wbr
    @4
    @39
    vk
    cF
    @35
    c1
    @38
    @41
    @45
    @39
    wph
    @70
    @26
    @24
    @46
    wcel
    @47
    @24
    @38
    elfznn
    climcnds.1
    syl2an
    @39
    @24
    @48
    wcel
    #
    wa
    wph
    @70
    @56
    wph
    @36
    @95
    simpll
    @39
    @38
    cn
    wcel
    #
    @24
    @38
    wceq
    #
    @70
    @95
    @36
    @96
    wph
    @35
    peano2nn
    #
    adantl
    @24
    @38
    elfz1eq
    @97
    @70
    @96
    @24
    @38
    cn
    eleq1
    biimparc
    syl2an
    climcnds.2
    syl2anc
    sermono
    adantlr
    @91
    cn0
    @14
    vn
    csu
    #
    cr
    wcel
    #
    @94
    @99
    cle
    wbr
    #
    vj
    cn
    wral
    #
    @94
    @65
    cle
    wbr
    #
    vj
    cn
    wral
    #
    vx
    cr
    wrex
    @91
    @14
    vn
    cG
    cc0
    cn0
    nn0uz
    @91
    0zd
    @91
    @13
    wa
    @14
    eqidd
    wph
    @13
    @15
    @4
    @32
    adantlr
    wph
    @4
    simpr
    isumrecl
    #
    @91
    @101
    vj
    cn
    @91
    @36
    wa
    #
    @94
    @35
    @3
    cfv
    #
    @99
    @91
    cn
    cr
    @35
    @0
    @93
    ffvelrnda
    #
    @91
    cn0
    cr
    @3
    wf
    #
    @53
    @107
    cr
    wcel
    @36
    wph
    @109
    @4
    wph
    vn
    cG
    cc0
    cn0
    nn0uz
    wph
    0zd
    @32
    serfre
    adantr
    @54
    cn0
    cr
    @35
    @3
    ffvelrn
    syl2an
    #
    @91
    @100
    @36
    @105
    adantr
    @106
    @94
    c2
    @38
    cexp
    co
    #
    c1
    cmin
    co
    #
    @0
    cfv
    #
    @107
    @108
    @106
    cn
    cr
    @112
    @0
    @91
    @79
    @36
    @93
    adantr
    @106
    @36
    @112
    @43
    wcel
    #
    @112
    cn
    wcel
    @91
    @36
    simpr
    @106
    @42
    @111
    @38
    cuz
    cfv
    #
    wcel
    #
    @114
    @36
    @42
    @91
    @44
    adantl
    #
    @106
    @116
    @38
    @111
    cle
    wbr
    #
    @106
    @38
    @111
    @106
    @38
    @36
    @52
    @91
    @55
    adantl
    #
    nn0red
    @106
    @111
    @106
    @20
    @52
    @111
    cn
    wcel
    2nn
    @119
    c2
    @38
    nnexpcl
    sylancr
    #
    nnred
    @106
    c2
    c2
    cuz
    cfv
    wcel
    #
    @52
    @38
    @111
    clt
    wbr
    c2
    cz
    wcel
    @121
    2z
    c2
    uzid
    ax-mp
    @119
    c2
    @38
    bernneq3
    sylancr
    ltled
    @106
    @38
    cz
    wcel
    @111
    cz
    wcel
    @116
    @118
    wb
    @106
    @35
    @117
    peano2zd
    @106
    @111
    @120
    nnzd
    @38
    @111
    eluz
    syl2anc
    mpbird
    @35
    @111
    eluzp1m1
    syl2anc
    #
    @112
    @35
    eluznn
    syl2anc
    ffvelrnd
    @110
    @106
    vk
    cF
    @35
    c1
    @112
    wph
    @36
    @35
    @40
    wcel
    @4
    @41
    adantlr
    @122
    @106
    wph
    @70
    @26
    @24
    c1
    @112
    cfz
    co
    wcel
    wph
    @4
    @36
    simpll
    #
    @24
    @112
    elfznn
    climcnds.1
    syl2an
    @106
    @24
    @38
    @112
    cfz
    co
    wcel
    #
    wa
    wph
    @70
    @56
    @106
    wph
    @124
    @123
    adantr
    @106
    @96
    @24
    @115
    wcel
    @70
    @124
    @36
    @96
    @91
    @98
    adantl
    @24
    @38
    @112
    elfzuz
    @24
    @38
    eluznn
    syl2an
    climcnds.2
    syl2anc
    sermono
    @106
    wph
    @53
    @113
    @107
    cle
    wbr
    @123
    @36
    @53
    @91
    @54
    adantl
    #
    wph
    vk
    vn
    cF
    cG
    @35
    climcnds.1
    climcnds.2
    climcnds.3
    climcnds.4
    climcndslem1
    syl2anc
    letrd
    @106
    cc0
    @35
    cfz
    co
    #
    @14
    vn
    csu
    @107
    @99
    cle
    @106
    @14
    vn
    cG
    cc0
    @35
    @106
    @11
    @126
    wcel
    #
    wa
    @14
    eqidd
    @106
    @35
    cn0
    cc0
    cuz
    cfv
    @125
    nn0uz
    syl6eleq
    @106
    wph
    @13
    @14
    cc
    wcel
    @127
    @123
    @11
    @35
    elfznn0
    #
    @90
    syl2an
    fsumser
    @106
    @126
    @14
    vn
    cG
    cc0
    cn0
    nn0uz
    @106
    0zd
    @106
    cc0
    @35
    fzfid
    @126
    cn0
    wss
    @106
    vn
    @126
    cn0
    @128
    ssriv
    a1i
    @106
    @13
    wa
    @14
    eqidd
    @106
    wph
    @13
    @15
    @123
    @32
    sylan
    @106
    wph
    @13
    @51
    @123
    @59
    sylan
    wph
    @4
    @36
    simplr
    isumless
    eqbrtrrd
    letrd
    ralrimiva
    @104
    @102
    vx
    @99
    cr
    @65
    @99
    wceq
    @103
    @101
    vj
    cn
    @65
    @99
    @94
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    climsup
    @0
    @92
    cli
    climrel
    releldmi
    syl
    impbida
end
