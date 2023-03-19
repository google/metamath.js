include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "ccnv.mm"
include "cfz.mm"
include "cima.mm"
include "chash.mm"
include "cli.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "wi.mm"
include "cle.mm"
include "nnz.mm"
include "ad2antlr.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "fzfid.mm"
include "crn.mm"
include "cin.mm"
include "wf.mm"
include "wfun.mm"
include "wceq.mm"
include "ffun.mm"
include "funimacnv.mm"
include "3syl.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "ad2antrr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashcl.mm"
include "nn0z.mm"
include "cen.mm"
include "wf1.mm"
include "wiso.mm"
include "wf1o.mm"
include "cres.mm"
include "ssid.mm"
include "isercolllem1.mm"
include "mpan2.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fnresdm.mm"
include "isoeq1.mm"
include "4syl.mm"
include "mpbid.mm"
include "isof1o.mm"
include "f1ocnv.mm"
include "f1ofun.mm"
include "df-f1.mm"
include "sylanbrc.mm"
include "elfznn.mm"
include "ssriv.mm"
include "ovex.mm"
include "f1imaen.mm"
include "sylancl.mm"
include "enfii.mm"
include "hashen.mm"
include "mpbird.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "syl.mm"
include "eqtrd.mm"
include "cdom.mm"
include "adantl.mm"
include "cr.mm"
include "zssre.mm"
include "sstri.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eluzelz.mm"
include "zred.mm"
include "elfzle2.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "isorel.mm"
include "syl12anc.mm"
include "notbid.mm"
include "nnred.mm"
include "lenltd.mm"
include "3bitr4d.mm"
include "eluzle.mm"
include "letrd.mm"
include "syl6eleq.mm"
include "elfz5.mm"
include "adantr.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"
include "imass2.mm"
include "ssdomg.mm"
include "sylc.mm"
include "hashdom.mm"
include "eqbrtrrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "ralrimdva.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "1nn.mm"
include "eqid.mm"
include "rexuz3.mm"
include "sylibrd.mm"
include "nn0p1nn.mm"
include "zltp1le.mm"
include "nn0re.mm"
include "eluznn.mm"
include "sylan.mm"
include "ltnled.mm"
include "fzss2.mm"
include "ffvelrnd.mm"
include "cxr.mm"
include "nnssre.mm"
include "ressxr.mm"
include "a1i.mm"
include "imassrn.mm"
include "frn.mm"
include "syl6ss.mm"
include "syl5ss.mm"
include "simpr.mm"
include "leisorel.mm"
include "syl122anc.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "fznn.mm"
include "eqrdv.mm"
include "imaeq2d.mm"
include "sseq1d.mm"
include "bitr3d.mm"
include "3imtr4d.mm"
include "syl5.mm"
include "mtod.mm"
include "wo.mm"
include "uztric.mm"
include "ord.mm"
include "mpd.mm"
include "oveq2.mm"
include "sylibd.mm"
include "impbid.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "seqex.mm"
include "eqidd.mm"
include "clim2.mm"
include "isercolllem3.mm"

theorem isercoll
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cS: class S
  assume isercoll.z: |- Z = ( ZZ>= ` M )
  assume isercoll.m: |- ( ph -> M e. ZZ )
  assume isercoll.g: |- ( ph -> G : NN --> Z )
  assume isercoll.i: |- ( ( ph /\ k e. NN ) -> ( G ` k ) < ( G ` ( k + 1 ) ) )
  assume isercoll.0: |- ( ( ph /\ n e. ( Z \ ran G ) ) -> ( F ` n ) = 0 )
  assume isercoll.f: |- ( ( ph /\ n e. Z ) -> ( F ` n ) e. CC )
  assume isercoll.h: |- ( ( ph /\ k e. NN ) -> ( H ` k ) = ( F ` ( G ` k ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  disjoint F n
  disjoint k ph
  disjoint n ph
  disjoint G k
  disjoint G n
  disjoint H k
  disjoint H n
  disjoint M k
  disjoint M n
  disjoint Z n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A x
  disjoint F j
  disjoint F m
  disjoint F x
  disjoint k y
  disjoint N k
  disjoint n y
  disjoint N n
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint j y
  disjoint j ph
  disjoint m y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint G j
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint H j
  disjoint H m
  disjoint H x
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( seq 1 ( + , H ) ~~> A <-> seq M ( + , F ) ~~> A ) )

  proof
    wph
    cA
    cc
    wcel
    #
    vk
    cv
    #
    caddc
    cH
    c1
    cseq
    #
    cfv
    #
    cc
    wcel
    #
    @3
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @0
    cG
    cG
    ccnv
    #
    cM
    vm
    cv
    #
    cfz
    co
    #
    cima
    #
    cima
    #
    chash
    cfv
    #
    @2
    cfv
    #
    cc
    wcel
    #
    @21
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vm
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    c1
    cG
    cfv
    #
    cuz
    cfv
    #
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @2
    cA
    cli
    wbr
    caddc
    cF
    cM
    cseq
    #
    cA
    cli
    wbr
    wph
    @14
    @33
    @0
    wph
    @13
    @32
    vx
    crp
    wph
    @13
    @32
    wph
    @13
    @29
    vj
    cz
    wrex
    #
    @32
    wph
    @12
    @35
    vn
    cn
    wph
    @10
    cn
    wcel
    #
    wa
    #
    @10
    cG
    cfv
    #
    cz
    wcel
    @12
    @26
    vm
    @38
    cuz
    cfv
    #
    wral
    #
    @35
    @37
    cZ
    cz
    @38
    cZ
    cM
    cuz
    cfv
    #
    cz
    isercoll.z
    cM
    uzssz
    eqsstri
    #
    wph
    cn
    cZ
    @10
    cG
    isercoll.g
    ffvelrnda
    #
    sseldi
    @37
    @12
    @26
    vm
    @39
    @37
    @16
    @39
    wcel
    #
    wa
    #
    @20
    @11
    wcel
    #
    @12
    @26
    wi
    @45
    @10
    cz
    wcel
    #
    @20
    cz
    wcel
    #
    @10
    @20
    cle
    wbr
    @46
    @36
    @47
    wph
    @44
    @10
    nnz
    ad2antlr
    @45
    @19
    cfn
    wcel
    #
    @20
    cn0
    wcel
    @48
    @45
    @17
    cfn
    wcel
    @19
    @17
    wss
    #
    @49
    @45
    cM
    @16
    fzfid
    wph
    @50
    @36
    @44
    wph
    @19
    @17
    cG
    crn
    #
    cin
    #
    @17
    wph
    cn
    cZ
    cG
    wf
    #
    cG
    wfun
    #
    @19
    @52
    wceq
    isercoll.g
    cn
    cZ
    cG
    ffun
    #
    @17
    cG
    funimacnv
    3syl
    @17
    @51
    inss1
    syl6eqss
    ad2antrr
    @17
    @19
    ssfi
    syl2anc
    #
    @19
    hashcl
    @20
    nn0z
    3syl
    @45
    cG
    c1
    @10
    cfz
    co
    #
    cima
    #
    chash
    cfv
    #
    @10
    @20
    cle
    @45
    @59
    @57
    chash
    cfv
    #
    @10
    @45
    @59
    @60
    wceq
    #
    @58
    @57
    cen
    wbr
    #
    @45
    cn
    cZ
    cG
    wf1
    #
    @57
    cn
    wss
    @62
    wph
    @63
    @36
    @44
    wph
    @53
    @15
    wfun
    #
    @63
    isercoll.g
    wph
    cn
    cG
    cn
    cima
    #
    clt
    clt
    cG
    wiso
    #
    cn
    @65
    cG
    wf1o
    @65
    cn
    @15
    wf1o
    @64
    wph
    cn
    @65
    clt
    clt
    cG
    cn
    cres
    #
    wiso
    #
    @66
    wph
    cn
    cn
    wss
    @68
    cn
    ssid
    wph
    cn
    vk
    cG
    cM
    cZ
    isercoll.z
    isercoll.m
    isercoll.g
    isercoll.i
    isercolllem1
    mpan2
    wph
    @53
    cG
    cn
    wfn
    #
    @67
    cG
    wceq
    @68
    @66
    wb
    isercoll.g
    cn
    cZ
    cG
    ffn
    #
    cn
    cG
    fnresdm
    cn
    @65
    clt
    clt
    cG
    @67
    isoeq1
    4syl
    mpbid
    #
    cn
    @65
    clt
    clt
    cG
    isof1o
    cn
    @65
    cG
    f1ocnv
    @65
    cn
    @15
    f1ofun
    4syl
    cn
    cZ
    cG
    df-f1
    sylanbrc
    #
    ad2antrr
    vy
    @57
    cn
    vy
    cv
    #
    @10
    elfznn
    #
    ssriv
    cn
    cZ
    @57
    cG
    c1
    @10
    cfz
    ovex
    f1imaen
    sylancl
    #
    @45
    @58
    cfn
    wcel
    #
    @57
    cfn
    wcel
    #
    @61
    @62
    wb
    @45
    @77
    @62
    @76
    @45
    c1
    @10
    fzfid
    #
    @75
    @58
    @57
    enfii
    syl2anc
    #
    @78
    @58
    @57
    hashen
    syl2anc
    mpbird
    @45
    @10
    cn0
    wcel
    #
    @60
    @10
    wceq
    @36
    @80
    wph
    @44
    @10
    nnnn0
    ad2antlr
    @10
    hashfz1
    syl
    eqtrd
    @45
    @59
    @20
    cle
    wbr
    #
    @58
    @19
    cdom
    wbr
    #
    @45
    @49
    @58
    @19
    wss
    #
    @82
    @56
    @45
    @57
    @18
    wss
    @83
    @45
    vy
    @57
    @18
    @45
    @73
    @57
    wcel
    #
    @73
    @18
    wcel
    #
    @45
    @84
    wa
    #
    @85
    @73
    cn
    wcel
    #
    @73
    cG
    cfv
    #
    @17
    wcel
    #
    @84
    @87
    @45
    @74
    adantl
    #
    @86
    @89
    @88
    @16
    cle
    wbr
    #
    @86
    @88
    @38
    @16
    @86
    cZ
    cr
    @88
    cZ
    cz
    cr
    @42
    zssre
    sstri
    #
    @45
    @53
    @87
    @88
    cZ
    wcel
    @84
    wph
    @53
    @36
    @44
    isercoll.g
    ad2antrr
    #
    @74
    cn
    cZ
    @73
    cG
    ffvelrn
    syl2an
    #
    sseldi
    #
    @86
    cZ
    cr
    @38
    @92
    @37
    @38
    cZ
    wcel
    @44
    @84
    @43
    ad2antrr
    sseldi
    #
    @86
    @16
    @44
    @16
    cz
    wcel
    #
    @37
    @84
    @38
    @16
    eluzelz
    ad2antlr
    #
    zred
    @86
    @73
    @10
    cle
    wbr
    #
    @88
    @38
    cle
    wbr
    #
    @84
    @99
    @45
    @73
    c1
    @10
    elfzle2
    adantl
    @86
    @10
    @73
    clt
    wbr
    #
    wn
    @38
    @88
    clt
    wbr
    #
    wn
    @99
    @100
    @86
    @101
    @102
    @86
    @66
    @36
    @87
    @101
    @102
    wb
    wph
    @66
    @36
    @44
    @84
    @71
    ad3antrrr
    wph
    @36
    @44
    @84
    simpllr
    #
    @90
    cn
    @65
    @10
    @73
    clt
    clt
    cG
    isorel
    syl12anc
    notbid
    @86
    @73
    @10
    @86
    @73
    @90
    nnred
    @86
    @10
    @103
    nnred
    lenltd
    @86
    @88
    @38
    @95
    @96
    lenltd
    3bitr4d
    mpbid
    @44
    @38
    @16
    cle
    wbr
    @37
    @84
    @38
    @16
    eluzle
    ad2antlr
    letrd
    @86
    @88
    @41
    wcel
    @97
    @89
    @91
    wb
    @86
    @88
    cZ
    @41
    @94
    isercoll.z
    syl6eleq
    @98
    @88
    cM
    @16
    elfz5
    syl2anc
    mpbird
    @86
    @69
    @85
    @87
    @89
    wa
    wb
    @45
    @69
    @84
    @45
    @53
    @69
    @93
    @70
    syl
    adantr
    cn
    @73
    @17
    cG
    elpreima
    syl
    mpbir2and
    ex
    ssrdv
    @57
    @18
    cG
    imass2
    syl
    @58
    @19
    cfn
    ssdomg
    sylc
    @45
    @76
    @49
    @81
    @82
    wb
    @79
    @56
    @58
    @19
    cfn
    hashdom
    syl2anc
    mpbird
    eqbrtrrd
    @10
    @20
    eluz2
    syl3anbrc
    @9
    @26
    vk
    @20
    @11
    @1
    @20
    wceq
    #
    @4
    @22
    @8
    @25
    @104
    @3
    @21
    cc
    @1
    @20
    @2
    fveq2
    #
    eleq1d
    @104
    @6
    @24
    @7
    clt
    @104
    @5
    @23
    cabs
    @104
    @3
    @21
    cA
    cmin
    @105
    oveq1d
    fveq2d
    breq1d
    anbi12d
    rspcv
    syl
    ralrimdva
    @29
    @40
    vj
    @38
    cz
    @27
    @38
    wceq
    @26
    vm
    @28
    @39
    @27
    @38
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    rexlimdva
    wph
    @30
    @41
    wcel
    #
    @30
    cz
    wcel
    #
    @32
    @35
    wb
    wph
    @30
    cZ
    @41
    wph
    @53
    c1
    cn
    wcel
    @30
    cZ
    wcel
    isercoll.g
    1nn
    cn
    cZ
    c1
    cG
    ffvelrn
    sylancl
    isercoll.z
    syl6eleq
    #
    cM
    @30
    eluzelz
    #
    @26
    vj
    vm
    @30
    @31
    @31
    eqid
    #
    rexuz3
    3syl
    sylibrd
    wph
    @29
    @13
    vj
    @31
    wph
    @27
    @31
    wcel
    #
    wa
    #
    cG
    @15
    cM
    @27
    cfz
    co
    #
    cima
    #
    cima
    #
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @29
    @9
    vk
    @117
    cuz
    cfv
    #
    wral
    #
    @13
    @112
    @115
    cfn
    wcel
    #
    @116
    cn0
    wcel
    #
    @118
    @112
    @113
    cfn
    wcel
    @115
    @113
    wss
    #
    @121
    @112
    cM
    @27
    fzfid
    wph
    @123
    @111
    wph
    @115
    @113
    @51
    cin
    #
    @113
    wph
    @53
    @54
    @115
    @124
    wceq
    isercoll.g
    @55
    @113
    cG
    funimacnv
    3syl
    @113
    @51
    inss1
    syl6eqss
    adantr
    @113
    @115
    ssfi
    syl2anc
    #
    @115
    hashcl
    #
    @116
    nn0p1nn
    3syl
    #
    @112
    @29
    @9
    vk
    @119
    @112
    @1
    @119
    wcel
    #
    wa
    #
    @29
    cG
    @15
    cM
    @1
    cG
    cfv
    #
    cfz
    co
    #
    cima
    #
    cima
    #
    chash
    cfv
    #
    @2
    cfv
    #
    cc
    wcel
    #
    @135
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    @9
    @129
    @130
    @28
    wcel
    #
    @29
    @140
    wi
    @129
    @27
    @130
    cuz
    cfv
    wcel
    #
    wn
    @141
    @129
    @142
    @1
    @116
    cle
    wbr
    #
    @129
    @116
    @1
    clt
    wbr
    #
    @143
    wn
    @129
    @144
    @117
    @1
    cle
    wbr
    #
    @128
    @145
    @112
    @117
    @1
    eluzle
    adantl
    @129
    @116
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @144
    @145
    wb
    @129
    @121
    @122
    @146
    @112
    @121
    @128
    @125
    adantr
    #
    @126
    @116
    nn0z
    3syl
    @128
    @147
    @112
    @117
    @1
    eluzelz
    adantl
    #
    @116
    @1
    zltp1le
    syl2anc
    mpbird
    @129
    @116
    @1
    @112
    @116
    cr
    wcel
    #
    @128
    @112
    @121
    @122
    @150
    @125
    @126
    @116
    nn0re
    3syl
    adantr
    @129
    @1
    @112
    @118
    @128
    @1
    cn
    wcel
    #
    @127
    @1
    @117
    eluznn
    sylan
    #
    nnred
    ltnled
    mpbid
    @142
    @133
    @115
    wss
    #
    @129
    @143
    @142
    @131
    @113
    wss
    @132
    @114
    wss
    @153
    @130
    cM
    @27
    fzss2
    @131
    @113
    @15
    imass2
    @132
    @114
    cG
    imass2
    3syl
    @129
    cG
    c1
    @1
    cfz
    co
    #
    cima
    #
    @115
    wss
    #
    @155
    @115
    cdom
    wbr
    #
    @153
    @143
    @129
    @121
    @156
    @157
    wi
    @148
    @155
    @115
    cfn
    ssdomg
    syl
    @129
    @133
    @155
    @115
    @129
    @132
    @154
    cG
    @129
    vx
    @132
    @154
    @129
    @7
    cn
    wcel
    #
    @7
    cG
    cfv
    #
    @131
    wcel
    #
    wa
    #
    @158
    @7
    @1
    cle
    wbr
    #
    wa
    #
    @7
    @132
    wcel
    #
    @7
    @154
    wcel
    #
    @129
    @158
    @160
    @162
    @129
    @158
    wa
    #
    @160
    @159
    @130
    cle
    wbr
    #
    @162
    @166
    @159
    @41
    wcel
    @130
    cz
    wcel
    #
    @160
    @167
    wb
    @166
    @159
    cZ
    @41
    @129
    cn
    cZ
    @7
    cG
    wph
    @53
    @111
    @128
    isercoll.g
    ad2antrr
    #
    ffvelrnda
    isercoll.z
    syl6eleq
    @129
    @168
    @158
    @129
    cZ
    cz
    @130
    @42
    @129
    cn
    cZ
    @1
    cG
    @169
    @152
    ffvelrnd
    sseldi
    #
    adantr
    @159
    cM
    @130
    elfz5
    syl2anc
    @166
    @66
    cn
    cxr
    wss
    #
    @65
    cxr
    wss
    @158
    @151
    @162
    @167
    wb
    wph
    @66
    @111
    @128
    @158
    @71
    ad3antrrr
    @171
    @166
    cn
    cr
    cxr
    nnssre
    ressxr
    sstri
    a1i
    @166
    @65
    cr
    cxr
    @166
    @65
    @51
    cr
    cG
    cn
    imassrn
    @166
    @51
    cZ
    cr
    @166
    @53
    @51
    cZ
    wss
    @129
    @53
    @158
    @169
    adantr
    cn
    cZ
    cG
    frn
    syl
    @92
    syl6ss
    syl5ss
    ressxr
    syl6ss
    @129
    @158
    simpr
    @129
    @151
    @158
    @152
    adantr
    cn
    @65
    @7
    @1
    cG
    leisorel
    syl122anc
    bitr4d
    pm5.32da
    @129
    @53
    @69
    @164
    @161
    wb
    @169
    @70
    cn
    @7
    @131
    cG
    elpreima
    3syl
    @129
    @147
    @165
    @163
    wb
    @149
    @7
    @1
    fznn
    syl
    3bitr4d
    eqrdv
    imaeq2d
    #
    sseq1d
    @129
    @155
    chash
    cfv
    #
    @116
    cle
    wbr
    #
    @143
    @157
    @129
    @173
    @1
    @116
    cle
    @129
    @173
    @154
    chash
    cfv
    #
    @1
    @129
    @173
    @175
    wceq
    #
    @155
    @154
    cen
    wbr
    #
    @129
    @63
    @154
    cn
    wss
    @177
    wph
    @63
    @111
    @128
    @72
    ad2antrr
    vx
    @154
    cn
    @7
    @1
    elfznn
    ssriv
    cn
    cZ
    @154
    cG
    c1
    @1
    cfz
    ovex
    f1imaen
    sylancl
    #
    @129
    @155
    cfn
    wcel
    #
    @154
    cfn
    wcel
    #
    @176
    @177
    wb
    @129
    @180
    @177
    @179
    @129
    c1
    @1
    fzfid
    #
    @178
    @155
    @154
    enfii
    syl2anc
    #
    @181
    @155
    @154
    hashen
    syl2anc
    mpbird
    @129
    @151
    @1
    cn0
    wcel
    @175
    @1
    wceq
    @152
    @1
    nnnn0
    @1
    hashfz1
    3syl
    eqtrd
    #
    breq1d
    @129
    @179
    @121
    @174
    @157
    wb
    @182
    @148
    @155
    @115
    cfn
    hashdom
    syl2anc
    bitr3d
    3imtr4d
    syl5
    mtod
    @129
    @142
    @141
    @129
    @168
    @27
    cz
    wcel
    #
    @142
    @141
    wo
    @170
    @111
    @184
    wph
    @128
    @30
    @27
    eluzelz
    ad2antlr
    @130
    @27
    uztric
    syl2anc
    ord
    mpd
    @26
    @140
    vm
    @130
    @28
    @16
    @130
    wceq
    #
    @22
    @136
    @25
    @139
    @185
    @21
    @135
    cc
    @185
    @20
    @134
    @2
    @185
    @19
    @133
    chash
    @185
    @18
    @132
    cG
    @185
    @17
    @131
    @15
    @16
    @130
    cM
    cfz
    oveq2
    imaeq2d
    imaeq2d
    fveq2d
    fveq2d
    #
    eleq1d
    @185
    @24
    @138
    @7
    clt
    @185
    @23
    @137
    cabs
    @185
    @21
    @135
    cA
    cmin
    @186
    oveq1d
    fveq2d
    breq1d
    anbi12d
    rspcv
    syl
    @129
    @136
    @4
    @139
    @8
    @129
    @135
    @3
    cc
    @129
    @134
    @1
    @2
    @129
    @134
    @173
    @1
    @129
    @133
    @155
    chash
    @172
    fveq2d
    @183
    eqtrd
    fveq2d
    #
    eleq1d
    @129
    @138
    @6
    @7
    clt
    @129
    @137
    @5
    cabs
    @129
    @135
    @3
    cA
    cmin
    @187
    oveq1d
    fveq2d
    breq1d
    anbi12d
    sylibd
    ralrimdva
    @12
    @120
    vn
    @117
    cn
    @10
    @117
    wceq
    @9
    vk
    @11
    @119
    @10
    @117
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    rexlimdva
    impbid
    ralbidv
    anbi2d
    wph
    vx
    cA
    @3
    vn
    vk
    @2
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    @2
    cvv
    wcel
    wph
    caddc
    cH
    c1
    seqex
    a1i
    wph
    @151
    wa
    @3
    eqidd
    clim2
    wph
    vx
    cA
    @21
    vj
    vm
    @34
    @30
    cvv
    @31
    @110
    wph
    @106
    @107
    @108
    @109
    syl
    @34
    cvv
    wcel
    wph
    caddc
    cF
    cM
    seqex
    a1i
    wph
    vk
    vn
    cF
    cG
    cH
    cM
    @16
    cZ
    isercoll.z
    isercoll.m
    isercoll.g
    isercoll.i
    isercoll.0
    isercoll.f
    isercoll.h
    isercolllem3
    clim2
    3bitr4d
end
