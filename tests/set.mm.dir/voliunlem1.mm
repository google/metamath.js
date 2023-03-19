include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "ciun.mm"
include "cin.mm"
include "covol.mm"
include "crn.mm"
include "cuni.mm"
include "cdif.mm"
include "caddc.mm"
include "cseq.mm"
include "cle.mm"
include "cr.mm"
include "wss.mm"
include "adantr.mm"
include "difss.mm"
include "ovolsscl.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "inss1.mm"
include "wbr.mm"
include "wral.mm"
include "elfznn.mm"
include "wfn.mm"
include "cvol.mm"
include "cdm.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "elssuni.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "sscond.mm"
include "syl5ss.mm"
include "ovolss.mm"
include "leadd2dd.mm"
include "wceq.mm"
include "wi.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "eleq1d.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "csn.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "iuneq1.mm"
include "mp2b.mm"
include "1ex.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "seq1.mm"
include "ineq2i.mm"
include "fveq2i.mm"
include "3eqtr4ri.mm"
include "jctir.mm"
include "cun.mm"
include "peano2nn.mm"
include "syl2an.mm"
include "unmbl.mm"
include "ex.mm"
include "syl5com.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzsuc.mm"
include "3syl.mm"
include "iunxun.mm"
include "ovex.mm"
include "uneq2i.mm"
include "syl6eq.mm"
include "sylibrd.mm"
include "oveq1.mm"
include "mblsplit.mm"
include "syl3anc.mm"
include "in32.mm"
include "inss2.mm"
include "adantl.mm"
include "eluzfz2.mm"
include "ssiun2s.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "indif2.mm"
include "uncom.mm"
include "syl6req.mm"
include "c0.mm"
include "wb.mm"
include "wdisj.mm"
include "wne.mm"
include "ad2antrr.mm"
include "nnred.mm"
include "clt.mm"
include "elfzle2.mm"
include "nnleltp1.mm"
include "mpbid.mm"
include "gtned.mm"
include "disji2.mm"
include "syl121anc.mm"
include "iuneq2dv.mm"
include "iunin2.mm"
include "iun0.mm"
include "3eqtr3g.mm"
include "uneqdifeq.mm"
include "syl5eqr.mm"
include "oveq12d.mm"
include "recnd.mm"
include "addcomd.mm"
include "3eqtrd.mm"
include "seqp1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "anim12d.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "simprd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "simpld.mm"
include "3brtr4d.mm"

theorem voliunlem1
  let wph: wff ph
  let vi: setvar i
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let vz: setvar z
  let vx: setvar x
  let cG: class G
  let cS: class S
  assume voliunlem.3: |- ( ph -> F : NN --> dom vol )
  assume voliunlem.5: |- ( ph -> Disj_ i e. NN ( F ` i ) )
  assume voliunlem1.6: |- H = ( n e. NN |-> ( vol* ` ( E i^i ( F ` n ) ) ) )
  assume voliunlem1.7: |- ( ph -> E C_ RR )
  assume voliunlem1.8: |- ( ph -> ( vol* ` E ) e. RR )

  disjoint k n
  disjoint E k
  disjoint E n
  disjoint i k
  disjoint i n
  disjoint F i
  disjoint F k
  disjoint F n
  disjoint H k
  disjoint k ph
  disjoint n ph
  disjoint k z
  disjoint n z
  disjoint E z
  disjoint i x
  disjoint i z
  disjoint k x
  disjoint n x
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G k
  disjoint H z
  disjoint S k
  disjoint S x
  disjoint S z
  disjoint ph x
  disjoint ph z
  assert |- ( ( ph /\ k e. NN ) -> ( ( seq 1 ( + , H ) ` k ) + ( vol* ` ( E \ U. ran F ) ) ) <_ ( vol* ` E ) )

  proof
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    cE
    vn
    c1
    @0
    cfz
    co
    #
    vn
    cv
    #
    cF
    cfv
    #
    ciun
    #
    cin
    #
    covol
    cfv
    #
    cE
    cF
    crn
    #
    cuni
    #
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    @8
    cE
    @6
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @0
    caddc
    cH
    c1
    cseq
    #
    cfv
    #
    @12
    caddc
    co
    cE
    covol
    cfv
    #
    cle
    @2
    @12
    @14
    @8
    @2
    cE
    cr
    wss
    #
    @18
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    wph
    @19
    @1
    voliunlem1.7
    adantr
    #
    wph
    @20
    @1
    voliunlem1.8
    adantr
    #
    @11
    cE
    wss
    @19
    @20
    @21
    cE
    @10
    difss
    @11
    cE
    ovolsscl
    mp3an1
    syl2anc
    @2
    @19
    @20
    @14
    cr
    wcel
    #
    @22
    @23
    @13
    cE
    wss
    @19
    @20
    @24
    cE
    @6
    difss
    #
    @13
    cE
    ovolsscl
    mp3an1
    syl2anc
    @2
    @19
    @20
    @8
    cr
    wcel
    #
    @22
    @23
    @7
    cE
    wss
    @19
    @20
    @26
    cE
    @6
    inss1
    @7
    cE
    ovolsscl
    mp3an1
    syl2anc
    #
    @2
    @11
    @13
    wss
    @13
    cr
    wss
    @12
    @14
    cle
    wbr
    @2
    @6
    @10
    cE
    @2
    @5
    @10
    wss
    #
    vn
    @3
    wral
    #
    @6
    @10
    wss
    wph
    @29
    @1
    wph
    @28
    vn
    @3
    @4
    @3
    wcel
    #
    wph
    @4
    cn
    wcel
    #
    @28
    @4
    @0
    elfznn
    #
    wph
    @31
    wa
    @5
    @9
    wcel
    #
    @28
    wph
    cF
    cn
    wfn
    #
    @31
    @33
    wph
    cn
    cvol
    cdm
    #
    cF
    wf
    #
    @34
    voliunlem.3
    cn
    @35
    cF
    ffn
    syl
    cn
    @4
    cF
    fnfvelrn
    sylan
    @5
    @9
    elssuni
    syl
    sylan2
    ralrimiva
    adantr
    vn
    @3
    @5
    @10
    iunss
    sylibr
    sscond
    @2
    @13
    cE
    cr
    @25
    @22
    syl5ss
    @11
    @13
    ovolss
    syl2anc
    leadd2dd
    @2
    @17
    @8
    @12
    caddc
    @2
    @8
    @17
    @2
    @6
    @35
    wcel
    #
    @8
    @17
    wceq
    #
    @1
    wph
    @37
    @38
    wa
    #
    wph
    vn
    c1
    vz
    cv
    #
    cfz
    co
    #
    @5
    ciun
    #
    @35
    wcel
    #
    cE
    @42
    cin
    #
    covol
    cfv
    #
    @40
    @16
    cfv
    #
    wceq
    #
    wa
    #
    wi
    wph
    vn
    c1
    c1
    cfz
    co
    #
    @5
    ciun
    #
    @35
    wcel
    #
    cE
    @50
    cin
    #
    covol
    cfv
    #
    c1
    @16
    cfv
    #
    wceq
    #
    wa
    #
    wi
    wph
    @39
    wi
    #
    wph
    vn
    c1
    @0
    c1
    caddc
    co
    #
    cfz
    co
    #
    @5
    ciun
    #
    @35
    wcel
    #
    cE
    @60
    cin
    #
    covol
    cfv
    #
    @58
    @16
    cfv
    #
    wceq
    #
    wa
    #
    wi
    @57
    vz
    vk
    @0
    @40
    c1
    wceq
    #
    @48
    @56
    wph
    @67
    @43
    @51
    @47
    @55
    @67
    @42
    @50
    @35
    @67
    vn
    @41
    @49
    @5
    @40
    c1
    c1
    cfz
    oveq2
    iuneq1d
    #
    eleq1d
    @67
    @45
    @53
    @46
    @54
    @67
    @44
    @52
    covol
    @67
    @42
    @50
    cE
    @68
    ineq2d
    fveq2d
    @40
    c1
    @16
    fveq2
    eqeq12d
    anbi12d
    imbi2d
    @40
    @0
    wceq
    #
    @48
    @39
    wph
    @69
    @43
    @37
    @47
    @38
    @69
    @42
    @6
    @35
    @69
    vn
    @41
    @3
    @5
    @40
    @0
    c1
    cfz
    oveq2
    iuneq1d
    #
    eleq1d
    @69
    @45
    @8
    @46
    @17
    @69
    @44
    @7
    covol
    @69
    @42
    @6
    cE
    @70
    ineq2d
    fveq2d
    @40
    @0
    @16
    fveq2
    eqeq12d
    anbi12d
    imbi2d
    #
    @40
    @58
    wceq
    #
    @48
    @66
    wph
    @72
    @43
    @61
    @47
    @65
    @72
    @42
    @60
    @35
    @72
    vn
    @41
    @59
    @5
    @40
    @58
    c1
    cfz
    oveq2
    iuneq1d
    #
    eleq1d
    @72
    @45
    @63
    @46
    @64
    @72
    @44
    @62
    covol
    @72
    @42
    @60
    cE
    @73
    ineq2d
    fveq2d
    @40
    @58
    @16
    fveq2
    eqeq12d
    anbi12d
    imbi2d
    @71
    wph
    @51
    @55
    wph
    @50
    c1
    cF
    cfv
    #
    @35
    @50
    vn
    c1
    csn
    #
    @5
    ciun
    #
    @74
    c1
    cz
    wcel
    #
    @49
    @75
    wceq
    @50
    @76
    wceq
    1z
    c1
    fzsn
    vn
    @49
    @75
    @5
    iuneq1
    mp2b
    vn
    c1
    @5
    @74
    1ex
    @4
    c1
    cF
    fveq2
    #
    iunxsn
    eqtri
    #
    wph
    @36
    c1
    cn
    wcel
    #
    @74
    @35
    wcel
    voliunlem.3
    1nn
    cn
    @35
    c1
    cF
    ffvelrn
    sylancl
    syl5eqel
    c1
    cH
    cfv
    #
    cE
    @74
    cin
    #
    covol
    cfv
    #
    @54
    @53
    @80
    @81
    @83
    wceq
    1nn
    vn
    c1
    cE
    @5
    cin
    #
    covol
    cfv
    #
    @83
    cn
    cH
    @4
    c1
    wceq
    #
    @84
    @82
    covol
    @86
    @5
    @74
    cE
    @78
    ineq2d
    fveq2d
    voliunlem1.6
    @82
    covol
    fvex
    fvmpt
    ax-mp
    @77
    @54
    @81
    wceq
    1z
    caddc
    cH
    c1
    seq1
    ax-mp
    @52
    @82
    covol
    @50
    @74
    cE
    @79
    ineq2i
    fveq2i
    3eqtr4ri
    jctir
    @1
    wph
    @39
    @66
    wph
    @1
    @39
    @66
    wi
    @2
    @37
    @61
    @38
    @65
    @2
    @37
    @6
    @58
    cF
    cfv
    #
    cun
    #
    @35
    wcel
    #
    @61
    @2
    @87
    @35
    wcel
    #
    @37
    @89
    wph
    @36
    @58
    cn
    wcel
    #
    @90
    @1
    voliunlem.3
    @0
    peano2nn
    #
    cn
    @35
    @58
    cF
    ffvelrn
    syl2an
    #
    @37
    @90
    @89
    @6
    @87
    unmbl
    ex
    syl5com
    @2
    @60
    @88
    @35
    @2
    @60
    vn
    @3
    @58
    csn
    #
    cun
    #
    @5
    ciun
    #
    @88
    @2
    @0
    c1
    cuz
    cfv
    #
    wcel
    #
    @59
    @95
    wceq
    @60
    @96
    wceq
    @2
    @0
    cn
    @97
    wph
    @1
    simpr
    #
    nnuz
    syl6eleq
    #
    c1
    @0
    fzsuc
    vn
    @59
    @95
    @5
    iuneq1
    3syl
    @96
    @6
    vn
    @94
    @5
    ciun
    #
    cun
    @88
    vn
    @3
    @94
    @5
    iunxun
    @101
    @87
    @6
    vn
    @58
    @5
    @87
    @0
    c1
    caddc
    ovex
    @4
    @58
    cF
    fveq2
    #
    iunxsn
    uneq2i
    eqtri
    syl6eq
    #
    eleq1d
    sylibrd
    @38
    @65
    @2
    @8
    cE
    @87
    cin
    #
    covol
    cfv
    #
    caddc
    co
    #
    @17
    @105
    caddc
    co
    #
    wceq
    @8
    @17
    @105
    caddc
    oveq1
    @2
    @63
    @106
    @64
    @107
    @2
    @63
    @62
    @87
    cin
    #
    covol
    cfv
    #
    @62
    @87
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @105
    @8
    caddc
    co
    @106
    @2
    @90
    @62
    cr
    wss
    @63
    cr
    wcel
    #
    @63
    @112
    wceq
    @93
    @2
    @62
    cE
    cr
    cE
    @60
    inss1
    #
    @22
    syl5ss
    @2
    @19
    @20
    @113
    @22
    @23
    @62
    cE
    wss
    @19
    @20
    @113
    @114
    @62
    cE
    ovolsscl
    mp3an1
    syl2anc
    @87
    @62
    mblsplit
    syl3anc
    @2
    @109
    @105
    @111
    @8
    caddc
    @2
    @108
    @104
    covol
    @2
    @108
    @104
    @60
    cin
    #
    @104
    cE
    @60
    @87
    in32
    @2
    @104
    @60
    wss
    @115
    @104
    wceq
    @2
    @104
    @87
    @60
    cE
    @87
    inss2
    @2
    @58
    @97
    wcel
    @58
    @59
    wcel
    @87
    @60
    wss
    #
    @2
    @58
    cn
    @97
    @1
    @91
    wph
    @92
    adantl
    #
    nnuz
    syl6eleq
    c1
    @58
    eluzfz2
    vn
    @59
    @5
    @58
    @87
    @102
    ssiun2s
    3syl
    #
    syl5ss
    @104
    @60
    df-ss
    sylib
    syl5eq
    fveq2d
    @2
    @110
    @7
    covol
    @2
    @110
    cE
    @60
    @87
    cdif
    #
    cin
    @7
    cE
    @60
    @87
    indif2
    @2
    @119
    @6
    cE
    @2
    @87
    @6
    cun
    #
    @60
    wceq
    #
    @119
    @6
    wceq
    #
    @2
    @60
    @88
    @120
    @103
    @6
    @87
    uncom
    syl6req
    @2
    @116
    @87
    @6
    cin
    #
    c0
    wceq
    @121
    @122
    wb
    @118
    @2
    vn
    @3
    @87
    @5
    cin
    #
    ciun
    vn
    @3
    c0
    ciun
    @123
    c0
    @2
    vn
    @3
    @124
    c0
    @2
    @30
    wa
    #
    vi
    cn
    vi
    cv
    #
    cF
    cfv
    #
    wdisj
    #
    @91
    @31
    @58
    @4
    wne
    @124
    c0
    wceq
    wph
    @128
    @1
    @30
    voliunlem.5
    ad2antrr
    @2
    @91
    @30
    @117
    adantr
    @30
    @31
    @2
    @32
    adantl
    #
    @125
    @4
    @58
    @125
    @4
    @129
    nnred
    @125
    @4
    @0
    cle
    wbr
    #
    @4
    @58
    clt
    wbr
    #
    @30
    @130
    @2
    @4
    c1
    @0
    elfzle2
    adantl
    @125
    @31
    @1
    @130
    @131
    wb
    @129
    @2
    @1
    @30
    @99
    adantr
    @4
    @0
    nnleltp1
    syl2anc
    mpbid
    gtned
    vi
    cn
    @127
    @87
    @5
    @58
    @4
    @126
    @58
    cF
    fveq2
    @126
    @4
    cF
    fveq2
    disji2
    syl121anc
    iuneq2dv
    vn
    @3
    @87
    @5
    iunin2
    vn
    @3
    iun0
    3eqtr3g
    @87
    @6
    @60
    uneqdifeq
    syl2anc
    mpbid
    ineq2d
    syl5eqr
    fveq2d
    oveq12d
    @2
    @105
    @8
    @2
    @105
    @2
    @19
    @20
    @105
    cr
    wcel
    #
    @22
    @23
    @104
    cE
    wss
    @19
    @20
    @132
    cE
    @87
    inss1
    @104
    cE
    ovolsscl
    mp3an1
    syl2anc
    recnd
    @2
    @8
    @27
    recnd
    addcomd
    3eqtrd
    @2
    @64
    @17
    @58
    cH
    cfv
    #
    caddc
    co
    #
    @107
    @2
    @98
    @64
    @134
    wceq
    @100
    caddc
    cH
    c1
    @0
    seqp1
    syl
    @2
    @133
    @105
    @17
    caddc
    @2
    @91
    @133
    @105
    wceq
    @117
    vn
    @58
    @85
    @105
    cn
    cH
    @4
    @58
    wceq
    #
    @84
    @104
    covol
    @135
    @5
    @87
    cE
    @102
    ineq2d
    fveq2d
    voliunlem1.6
    @104
    covol
    fvex
    fvmpt
    syl
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    anim12d
    expcom
    a2d
    nnind
    impcom
    #
    simprd
    eqcomd
    oveq1d
    @2
    @37
    @19
    @20
    @18
    @15
    wceq
    @2
    @37
    @38
    @136
    simpld
    @22
    @23
    @6
    cE
    mblsplit
    syl3anc
    3brtr4d
end
