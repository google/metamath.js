include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "wcel.mm"
include "wceq.mm"
include "cgsu.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "c0.mm"
include "noel.mm"
include "cres.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "wss.mm"
include "resss.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "dmeqi.mm"
include "dm0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "cfv.mm"
include "ccom.mm"
include "wf1o.mm"
include "wxo.mm"
include "cbs.mm"
include "cmnd.mm"
include "cword.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "eqid.mm"
include "symgtrf.mm"
include "sswrd.mm"
include "mp1i.mm"
include "sseldd.mm"
include "swrdcl.mm"
include "syl.mm"
include "gsumwcl.mm"
include "syl2anc.mm"
include "symgbasf1o.mm"
include "adantr.mm"
include "chash.mm"
include "wf.mm"
include "wrdf.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "wn.mm"
include "wo.mm"
include "cv.mm"
include "cvv.mm"
include "csn.mm"
include "crab.mm"
include "csubmnd.mm"
include "csubg.mm"
include "symgsssg.mm"
include "subgsubm.mm"
include "cmpt.mm"
include "cuz.mm"
include "cfz.mm"
include "fzossfz.mm"
include "elfzuz3.mm"
include "eqeltrd.mm"
include "fzoss2.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "wral.mm"
include "fveq2.mm"
include "notbid.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "difeq1.mm"
include "sseq1d.mm"
include "cin.mm"
include "disj2.mm"
include "disjsn.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fmptd.mm"
include "swrd0val.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "3eqtrd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "iswrdi.mm"
include "gsumwsubmcl.mm"
include "simprbi.mm"
include "jca.mm"
include "olcd.mm"
include "excxor.mm"
include "sylibr.mm"
include "f1omvdco3.mm"
include "syl3anc.mm"
include "cs1.mm"
include "cconcat.mm"
include "cplusg.mm"
include "cmin.mm"
include "clsw.mm"
include "wne.mm"
include "cn.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo0.mm"
include "simp2bi.mm"
include "cfn.mm"
include "wb.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "mpbid.mm"
include "swrdccatwrd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "1cnd.mm"
include "cz.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "subadd2d.mm"
include "biimpar.mm"
include "eqtrd.mm"
include "opeq2.mm"
include "adantl.mm"
include "lsw.mm"
include "sylan9eq.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "s1cld.mm"
include "gsumccat.mm"
include "gsumws1.mm"
include "symgov.mm"
include "mtand.mm"
include "fzostep1.mm"
include "ord.mm"
include "mt3d.mm"

theorem psgnunilem5
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cI: class I
  let cL: class L
  let cV: class V
  let cW: class W
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  assume psgnunilem2.g: |- G = ( SymGrp ` D )
  assume psgnunilem2.t: |- T = ran ( pmTrsp ` D )
  assume psgnunilem2.d: |- ( ph -> D e. V )
  assume psgnunilem2.w: |- ( ph -> W e. Word T )
  assume psgnunilem2.id: |- ( ph -> ( G gsum W ) = ( _I |` D ) )
  assume psgnunilem2.l: |- ( ph -> ( # ` W ) = L )
  assume psgnunilem2.ix: |- ( ph -> I e. ( 0 ..^ L ) )
  assume psgnunilem2.a: |- ( ph -> A e. dom ( ( W ` I ) \ _I ) )
  assume psgnunilem2.al: |- ( ph -> A. k e. ( 0 ..^ I ) -. A e. dom ( ( W ` k ) \ _I ) )

  disjoint A k
  disjoint G k
  disjoint I k
  disjoint W k
  disjoint j k
  disjoint j r
  disjoint j s
  disjoint j w
  disjoint A j
  disjoint k r
  disjoint k s
  disjoint k w
  disjoint r s
  disjoint r w
  disjoint A r
  disjoint s w
  disjoint A s
  disjoint A w
  disjoint j x
  disjoint D j
  disjoint r x
  disjoint D r
  disjoint s x
  disjoint D s
  disjoint w x
  disjoint D w
  disjoint D x
  disjoint j ph
  disjoint ph r
  disjoint ph s
  disjoint G j
  disjoint k x
  disjoint G r
  disjoint G s
  disjoint G w
  disjoint G x
  disjoint I j
  disjoint I r
  disjoint I s
  disjoint I w
  disjoint I x
  disjoint T j
  disjoint T r
  disjoint T s
  disjoint T w
  disjoint T x
  disjoint W j
  disjoint W r
  disjoint W s
  disjoint W w
  disjoint W x
  disjoint L r
  disjoint L s
  disjoint L w
  disjoint L x
  assert |- ( ph -> ( I + 1 ) e. ( 0 ..^ L ) )

  proof
    wph
    cI
    c1
    caddc
    co
    #
    cc0
    cL
    cfzo
    co
    #
    wcel
    #
    @0
    cL
    wceq
    #
    wph
    @3
    cA
    cG
    cW
    cgsu
    co
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wph
    @7
    cA
    c0
    wcel
    cA
    noel
    wph
    @6
    c0
    cA
    wph
    @6
    cid
    cD
    cres
    #
    cid
    cdif
    #
    cdm
    #
    c0
    wph
    @5
    @9
    wph
    @4
    @8
    cid
    psgnunilem2.id
    difeq1d
    dmeqd
    @10
    c0
    cdm
    c0
    @9
    c0
    @8
    cid
    wss
    @9
    c0
    wceq
    cid
    cD
    resss
    @8
    cid
    ssdif0
    mpbi
    dmeqi
    dm0
    eqtri
    syl6eq
    eleq2d
    mtbiri
    wph
    @3
    wa
    #
    cA
    cG
    cW
    cc0
    cI
    cop
    #
    csubstr
    co
    #
    cgsu
    co
    #
    cI
    cW
    cfv
    #
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    @6
    @11
    cD
    cD
    @14
    wf1o
    #
    cD
    cD
    @15
    wf1o
    #
    cA
    @14
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cA
    @15
    cid
    cdif
    cdm
    wcel
    #
    wxo
    #
    cA
    @18
    wcel
    wph
    @19
    @3
    wph
    @14
    cG
    cbs
    cfv
    #
    wcel
    #
    @19
    wph
    cG
    cmnd
    wcel
    #
    @13
    @26
    cword
    #
    wcel
    #
    @27
    wph
    cD
    cV
    wcel
    #
    cG
    cgrp
    wcel
    @28
    psgnunilem2.d
    cD
    cG
    cV
    psgnunilem2.g
    symggrp
    cG
    grpmnd
    3syl
    #
    wph
    cW
    @29
    wcel
    @30
    wph
    cT
    cword
    #
    @29
    cW
    cT
    @26
    wss
    @33
    @29
    wss
    wph
    @26
    cD
    cT
    cG
    psgnunilem2.t
    psgnunilem2.g
    @26
    eqid
    #
    symgtrf
    #
    cT
    @26
    sswrd
    mp1i
    psgnunilem2.w
    sseldd
    @26
    cW
    cc0
    cI
    swrdcl
    syl
    #
    @26
    cG
    @13
    @34
    gsumwcl
    syl2anc
    #
    cD
    @26
    @14
    cG
    psgnunilem2.g
    @34
    symgbasf1o
    syl
    adantr
    wph
    @20
    @3
    wph
    @15
    @26
    wcel
    #
    @20
    wph
    cT
    @26
    @15
    @35
    wph
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cT
    cI
    cW
    wph
    cW
    @33
    wcel
    #
    @40
    cT
    cW
    wf
    psgnunilem2.w
    cT
    cW
    wrdf
    syl
    #
    wph
    cI
    @1
    @40
    psgnunilem2.ix
    wph
    @39
    cL
    cc0
    cfzo
    psgnunilem2.l
    oveq2d
    eleqtrrd
    ffvelrnd
    sseldi
    #
    cD
    @26
    @15
    cG
    psgnunilem2.g
    @34
    symgbasf1o
    syl
    adantr
    @11
    @23
    @24
    wn
    wa
    #
    @23
    wn
    #
    @24
    wa
    #
    wo
    @25
    @11
    @46
    @44
    @11
    @45
    @24
    @11
    @14
    vj
    cv
    #
    cid
    cdif
    #
    cdm
    #
    cvv
    cA
    csn
    #
    cdif
    #
    wss
    #
    vj
    @26
    crab
    #
    wcel
    #
    @45
    @11
    @53
    cG
    csubmnd
    cfv
    wcel
    #
    @13
    @53
    cword
    wcel
    #
    @54
    wph
    @55
    @3
    wph
    @31
    @53
    cG
    csubg
    cfv
    wcel
    @55
    psgnunilem2.d
    vj
    @26
    cD
    cG
    cV
    @51
    psgnunilem2.g
    @34
    symgsssg
    @53
    cG
    subgsubm
    3syl
    adantr
    @11
    cc0
    cI
    cfzo
    co
    #
    @53
    @13
    wf
    #
    @56
    wph
    @58
    @3
    wph
    @58
    @57
    @53
    vs
    @57
    vs
    cv
    #
    cW
    cfv
    #
    cmpt
    #
    wf
    wph
    vs
    @57
    @60
    @53
    @61
    wph
    @59
    @57
    wcel
    #
    wa
    @60
    @26
    wcel
    #
    cA
    @60
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    @60
    @53
    wcel
    wph
    @62
    @59
    @40
    wcel
    #
    @63
    wph
    @57
    @40
    @59
    wph
    @39
    cI
    cuz
    cfv
    #
    wcel
    #
    @57
    @40
    wss
    #
    wph
    @39
    cL
    @69
    psgnunilem2.l
    wph
    cI
    cc0
    cL
    cfz
    co
    #
    wcel
    cL
    @69
    wcel
    wph
    @1
    @72
    cI
    cc0
    cL
    fzossfz
    psgnunilem2.ix
    sseldi
    #
    cI
    cc0
    cL
    elfzuz3
    syl
    eqeltrd
    #
    cI
    cc0
    @39
    fzoss2
    #
    syl
    sselda
    wph
    @68
    wa
    cT
    @26
    @60
    @35
    wph
    @40
    cT
    @59
    cW
    @42
    ffvelrnda
    sseldi
    syldan
    wph
    @67
    vs
    @57
    wph
    cA
    vk
    cv
    #
    cW
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vk
    @57
    wral
    @67
    vs
    @57
    wral
    psgnunilem2.al
    @81
    @67
    vk
    vs
    @57
    @76
    @59
    wceq
    #
    @80
    @66
    @82
    @79
    @65
    cA
    @82
    @78
    @64
    @82
    @77
    @60
    cid
    @76
    @59
    cW
    fveq2
    difeq1d
    dmeqd
    eleq2d
    notbid
    cbvralv
    sylib
    r19.21bi
    @52
    @67
    vj
    @60
    @26
    @47
    @60
    wceq
    #
    @52
    @65
    @51
    wss
    #
    @67
    @83
    @49
    @65
    @51
    @83
    @48
    @64
    @47
    @60
    cid
    difeq1
    dmeqd
    sseq1d
    @84
    @65
    @50
    cin
    c0
    wceq
    @67
    @65
    @50
    disj2
    @65
    cA
    disjsn
    bitr3i
    syl6bb
    elrab
    sylanbrc
    @61
    eqid
    fmptd
    wph
    @57
    @53
    @13
    @61
    wph
    @13
    cW
    @57
    cres
    #
    vs
    @40
    @60
    cmpt
    #
    @57
    cres
    #
    @61
    wph
    @41
    cI
    cc0
    @39
    cfz
    co
    #
    wcel
    @13
    @85
    wceq
    psgnunilem2.w
    wph
    cI
    @72
    @88
    @73
    wph
    @39
    cL
    cc0
    cfz
    psgnunilem2.l
    oveq2d
    eleqtrrd
    cT
    cW
    cI
    swrd0val
    syl2anc
    wph
    cW
    @86
    @57
    wph
    vs
    @40
    cT
    cW
    @42
    feqmptd
    reseq1d
    wph
    @70
    @71
    @87
    @61
    wceq
    @74
    @75
    vs
    @40
    @57
    @60
    resmpt
    3syl
    3eqtrd
    feq1d
    mpbird
    adantr
    @53
    cI
    @13
    iswrdi
    syl
    @53
    cG
    @13
    gsumwsubmcl
    syl2anc
    @54
    @22
    @51
    wss
    #
    @45
    @54
    @27
    @89
    @52
    @89
    vj
    @14
    @26
    @47
    @14
    wceq
    #
    @49
    @22
    @51
    @90
    @48
    @21
    @47
    @14
    cid
    difeq1
    dmeqd
    sseq1d
    elrab
    simprbi
    @89
    @22
    @50
    cin
    c0
    wceq
    @45
    @22
    @50
    disj2
    @22
    cA
    disjsn
    bitr3i
    sylib
    syl
    wph
    @24
    @3
    psgnunilem2.a
    adantr
    jca
    olcd
    @23
    @24
    excxor
    sylibr
    cD
    @14
    @15
    cA
    f1omvdco3
    syl3anc
    @11
    @5
    @17
    @11
    @4
    @16
    cid
    @11
    @4
    cG
    @13
    @15
    cs1
    #
    cconcat
    co
    #
    cgsu
    co
    #
    @14
    cG
    @91
    cgsu
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @16
    @11
    cW
    @92
    cG
    cgsu
    @11
    cW
    cW
    cc0
    @39
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    cW
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    @92
    @11
    @41
    cW
    c0
    wne
    #
    cW
    @102
    wceq
    wph
    @41
    @3
    psgnunilem2.w
    adantr
    wph
    @103
    @3
    wph
    @39
    cn
    wcel
    #
    @103
    wph
    @39
    cL
    cn
    psgnunilem2.l
    wph
    cI
    @1
    wcel
    #
    cL
    cn
    wcel
    #
    psgnunilem2.ix
    @105
    cI
    cn0
    wcel
    @106
    cI
    cL
    clt
    wbr
    cI
    cL
    elfzo0
    simp2bi
    syl
    #
    eqeltrd
    wph
    @41
    cW
    cfn
    wcel
    @104
    @103
    wb
    psgnunilem2.w
    cT
    cW
    wrdfin
    cW
    hashnncl
    3syl
    mpbid
    adantr
    @41
    @103
    wa
    @102
    cW
    cT
    cW
    swrdccatwrd
    eqcomd
    syl2anc
    wph
    @3
    @97
    cI
    wceq
    #
    @102
    @92
    wceq
    @11
    @97
    cL
    c1
    cmin
    co
    #
    cI
    wph
    @97
    @109
    wceq
    @3
    wph
    @39
    cL
    c1
    cmin
    psgnunilem2.l
    oveq1d
    adantr
    wph
    @109
    cI
    wceq
    @3
    wph
    cL
    c1
    cI
    wph
    cL
    @107
    nncnd
    wph
    1cnd
    wph
    cI
    wph
    @105
    cI
    cz
    wcel
    psgnunilem2.ix
    cI
    cc0
    cL
    elfzoelz
    syl
    zcnd
    subadd2d
    biimpar
    eqtrd
    wph
    @108
    wa
    #
    @99
    @13
    @101
    @91
    cconcat
    @108
    @99
    @13
    wceq
    wph
    @108
    @98
    @12
    cW
    csubstr
    @97
    cI
    cc0
    opeq2
    oveq2d
    adantl
    @110
    @100
    @15
    wph
    @108
    @100
    @97
    cW
    cfv
    #
    @15
    wph
    @41
    @100
    @111
    wceq
    psgnunilem2.w
    cW
    @33
    lsw
    syl
    @97
    cI
    cW
    fveq2
    sylan9eq
    s1eqd
    oveq12d
    syldan
    eqtrd
    oveq2d
    wph
    @93
    @96
    wceq
    #
    @3
    wph
    @28
    @30
    @91
    @29
    wcel
    @112
    @32
    @36
    wph
    @15
    @26
    @43
    s1cld
    @26
    @95
    cG
    @13
    @91
    @34
    @95
    eqid
    #
    gsumccat
    syl3anc
    adantr
    wph
    @96
    @16
    wceq
    @3
    wph
    @96
    @14
    @15
    @95
    co
    #
    @16
    wph
    @94
    @15
    @14
    @95
    wph
    @38
    @94
    @15
    wceq
    @43
    @26
    @15
    cG
    @34
    gsumws1
    syl
    oveq2d
    wph
    @27
    @38
    @114
    @16
    wceq
    @37
    @43
    cD
    @26
    @95
    cG
    @14
    @15
    psgnunilem2.g
    @34
    @113
    symgov
    syl2anc
    eqtrd
    adantr
    3eqtrd
    difeq1d
    dmeqd
    eleqtrrd
    mtand
    wph
    @2
    @3
    wph
    @105
    @2
    @3
    wo
    psgnunilem2.ix
    cI
    cc0
    cL
    fzostep1
    syl
    ord
    mt3d
end
