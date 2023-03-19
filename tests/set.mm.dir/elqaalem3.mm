include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "caa.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "wne.mm"
include "cdgr.mm"
include "cfz.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "wa.mm"
include "cseq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvexd.mm"
include "fconstmpt.mm"
include "cq.mm"
include "wf.mm"
include "eldifad.mm"
include "plyf.mm"
include "syl.mm"
include "feqmptd.mm"
include "offval2.mm"
include "fzfid.mm"
include "cn.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "crab.mm"
include "ssrab2.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ltso.mm"
include "infex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "c0.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "0z.mm"
include "zq.mm"
include "ax-mp.mm"
include "coef2.mm"
include "sylancl.mm"
include "ffvelrnda.mm"
include "qmulz.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "sseldi.mm"
include "nnmulcl.mm"
include "seqf.mm"
include "dgrcl.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "nncnd.mm"
include "adantr.mm"
include "elfznn0.mm"
include "coef3.mm"
include "expcl.mm"
include "adantll.mm"
include "mulcld.mm"
include "sylan2.mm"
include "fsummulc2.mm"
include "eqid.mm"
include "coeid2.mm"
include "sylan.mm"
include "oveq2d.mm"
include "mulassd.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "zsscn.mm"
include "cdiv.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "divcld.mm"
include "mulcomd.mm"
include "3eqtr4rd.mm"
include "oveq2.mm"
include "elrab.mm"
include "simprbi.mm"
include "cmo.mm"
include "cmpt2.mm"
include "elqaalem2.mm"
include "wb.mm"
include "crp.mm"
include "nnre.mm"
include "nnrp.mm"
include "mod0.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "zmulcld.mm"
include "elplyd.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "oveq1.mm"
include "divcan3d.mm"
include "ovexd.mm"
include "div0d.mm"
include "mpteq2dv.mm"
include "0cnd.mm"
include "df-0p.mm"
include "eqtri.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "necon3d.mm"
include "mpd.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "fconst.mm"
include "ffn.mm"
include "mp1i.mm"
include "inidm.mm"
include "fvconst2.mm"
include "ofval.mm"
include "mpdan.mm"
include "mul01d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "elaa.mm"

theorem elqaalem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let cK: class K
  assume elqaa.1: |- ( ph -> A e. CC )
  assume elqaa.2: |- ( ph -> F e. ( ( Poly ` QQ ) \ { 0p } ) )
  assume elqaa.3: |- ( ph -> ( F ` A ) = 0 )
  assume elqaa.4: |- B = ( coeff ` F )
  assume elqaa.5: |- N = ( k e. NN0 |-> inf ( { n e. NN | ( ( B ` k ) x. n ) e. ZZ } , RR , < ) )
  assume elqaa.6: |- R = ( seq 0 ( x. , N ) ` ( deg ` F ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint B k
  disjoint B n
  disjoint k ph
  disjoint N k
  disjoint N n
  disjoint R k
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B m
  disjoint B z
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint i k
  disjoint i m
  disjoint i z
  disjoint i ph
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint j ph
  disjoint m ph
  disjoint ph z
  disjoint f i
  disjoint f j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F m
  disjoint F z
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint R f
  disjoint R m
  disjoint R z
  assert |- ( ph -> A e. AA )

  proof
    wph
    cA
    cc
    wcel
    #
    cA
    vf
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vf
    cz
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    #
    wrex
    #
    cA
    caa
    wcel
    elqaa.1
    wph
    cc
    cR
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    co
    #
    @6
    wcel
    #
    cA
    @10
    cfv
    #
    cc0
    wceq
    #
    @7
    wph
    @10
    @4
    wcel
    @10
    c0p
    wne
    #
    @11
    wph
    @10
    vz
    cc
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    cR
    vm
    cv
    #
    cB
    cfv
    #
    cmul
    co
    #
    vz
    cv
    #
    @17
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmpt
    #
    @4
    wph
    @10
    vz
    cc
    cR
    @20
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    @24
    wph
    vz
    cc
    cR
    @25
    cmul
    @9
    cF
    cvv
    cvv
    cvv
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    #
    cR
    cvv
    wcel
    wph
    @20
    cc
    wcel
    #
    wa
    #
    cR
    @15
    cmul
    cN
    cc0
    cseq
    #
    cfv
    #
    cvv
    elqaa.6
    @15
    @30
    fvex
    eqeltri
    #
    a1i
    #
    @29
    @20
    cF
    fvexd
    @9
    vz
    cc
    cR
    cmpt
    wceq
    wph
    vz
    cc
    cR
    fconstmpt
    a1i
    #
    wph
    vz
    cc
    cc
    cF
    wph
    cF
    cq
    cply
    cfv
    #
    wcel
    #
    cc
    cc
    cF
    wf
    #
    wph
    cF
    @35
    @5
    elqaa.2
    eldifad
    #
    cq
    cF
    plyf
    syl
    #
    feqmptd
    #
    offval2
    #
    wph
    vz
    cc
    @26
    @23
    @29
    cR
    @16
    @18
    @21
    cmul
    co
    #
    vm
    csu
    #
    cmul
    co
    @16
    cR
    @42
    cmul
    co
    #
    vm
    csu
    @26
    @23
    @29
    @16
    @42
    cR
    vm
    @29
    cc0
    @15
    fzfid
    wph
    cR
    cc
    wcel
    #
    @28
    wph
    cR
    wph
    cR
    @31
    cn
    elqaa.6
    wph
    cn0
    cn
    @15
    @30
    wph
    vm
    vk
    cmul
    cn
    cN
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    @17
    cn0
    wcel
    #
    wa
    #
    @18
    vn
    cv
    #
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    cn
    @17
    cN
    cfv
    #
    @50
    vn
    cn
    ssrab2
    #
    @47
    @52
    @51
    cr
    clt
    cinf
    #
    @51
    @46
    @52
    @54
    wceq
    wph
    vk
    @17
    vk
    cv
    #
    cB
    cfv
    #
    @48
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    @54
    cn0
    cN
    @55
    @17
    wceq
    #
    cr
    @59
    @51
    clt
    @60
    @58
    @50
    vn
    cn
    @60
    @57
    @49
    cz
    @60
    @56
    @18
    @48
    cmul
    @55
    @17
    cB
    fveq2
    oveq1d
    eleq1d
    rabbidv
    infeq1d
    elqaa.5
    cr
    @51
    clt
    ltso
    infex
    fvmpt
    adantl
    @47
    @51
    c1
    cuz
    cfv
    #
    wss
    @51
    c0
    wne
    #
    @54
    @51
    wcel
    @51
    cn
    @61
    @53
    nnuz
    sseqtri
    @47
    @50
    vn
    cn
    wrex
    #
    @62
    @47
    @18
    cq
    wcel
    @63
    wph
    cn0
    cq
    @17
    cB
    wph
    @36
    cc0
    cq
    wcel
    #
    cn0
    cq
    cB
    wf
    @38
    cc0
    cz
    wcel
    @64
    0z
    cc0
    zq
    ax-mp
    cB
    cq
    cF
    elqaa.4
    coef2
    sylancl
    ffvelrnda
    vn
    @18
    qmulz
    syl
    @50
    vn
    cn
    rabn0
    sylibr
    @51
    c1
    infssuzcl
    sylancr
    eqeltrd
    #
    sseldi
    #
    @17
    cn
    wcel
    @55
    cn
    wcel
    wa
    @17
    @55
    cmul
    co
    cn
    wcel
    wph
    @17
    @55
    nnmulcl
    adantl
    seqf
    wph
    @36
    @15
    cn0
    wcel
    @38
    cq
    cF
    dgrcl
    syl
    #
    ffvelrnd
    syl5eqel
    #
    nncnd
    #
    adantr
    #
    @17
    @16
    wcel
    #
    @29
    @46
    @42
    cc
    wcel
    @17
    @15
    elfznn0
    #
    @29
    @46
    wa
    #
    @18
    @21
    @29
    cn0
    cc
    @17
    cB
    wph
    cn0
    cc
    cB
    wf
    #
    @28
    wph
    @36
    @74
    @38
    cB
    cq
    cF
    elqaa.4
    coef3
    syl
    #
    adantr
    ffvelrnda
    #
    @28
    @46
    @21
    cc
    wcel
    wph
    @20
    @17
    expcl
    adantll
    #
    mulcld
    sylan2
    fsummulc2
    @29
    @25
    @43
    cR
    cmul
    wph
    @36
    @28
    @25
    @43
    wceq
    @38
    cB
    cq
    vm
    cF
    @15
    @20
    elqaa.4
    @15
    eqid
    coeid2
    sylan
    oveq2d
    @29
    @16
    @22
    @44
    vm
    @71
    @29
    @46
    @22
    @44
    wceq
    @72
    @73
    cR
    @18
    @21
    @29
    @45
    @46
    @70
    adantr
    @76
    @77
    mulassd
    sylan2
    sumeq2dv
    3eqtr4d
    mpteq2dva
    eqtrd
    wph
    vz
    @19
    cz
    vm
    @15
    cz
    cc
    wss
    wph
    zsscn
    a1i
    @67
    wph
    @71
    wa
    #
    @19
    @18
    @52
    cmul
    co
    #
    cR
    @52
    cdiv
    co
    #
    cmul
    co
    #
    cz
    @71
    wph
    @46
    @19
    @81
    wceq
    @72
    @47
    @18
    @52
    @80
    cmul
    co
    #
    cmul
    co
    @18
    cR
    cmul
    co
    @81
    @19
    @47
    @82
    cR
    @18
    cmul
    @47
    cR
    @52
    wph
    @45
    @46
    @69
    adantr
    #
    @47
    @52
    @66
    nncnd
    #
    @47
    @52
    @66
    nnne0d
    #
    divcan2d
    oveq2d
    @47
    @18
    @52
    @80
    wph
    cn0
    cc
    @17
    cB
    @75
    ffvelrnda
    #
    @84
    @47
    cR
    @52
    @83
    @84
    @85
    divcld
    mulassd
    @47
    cR
    @18
    @83
    @86
    mulcomd
    3eqtr4rd
    sylan2
    @78
    @79
    @80
    @71
    wph
    @46
    @79
    cz
    wcel
    #
    @72
    @47
    @52
    @51
    wcel
    #
    @87
    @65
    @88
    @52
    cn
    wcel
    #
    @87
    @50
    @87
    vn
    @52
    cn
    @48
    @52
    wceq
    @49
    @79
    cz
    @48
    @52
    @18
    cmul
    oveq2
    eleq1d
    elrab
    simprbi
    syl
    sylan2
    @78
    cR
    @52
    cmo
    co
    cc0
    wceq
    #
    @80
    cz
    wcel
    #
    wph
    vx
    vy
    cA
    cB
    vx
    vy
    cvv
    cvv
    vx
    cv
    vy
    cv
    cmul
    co
    @52
    cmo
    co
    cmpt2
    #
    cR
    vk
    vn
    cF
    @17
    cN
    elqaa.1
    elqaa.2
    elqaa.3
    elqaa.4
    elqaa.5
    elqaa.6
    @92
    eqid
    elqaalem2
    @78
    cR
    cn
    wcel
    #
    @89
    @90
    @91
    wb
    #
    wph
    @93
    @71
    @68
    adantr
    @71
    wph
    @46
    @89
    @72
    @66
    sylan2
    @93
    cR
    cr
    wcel
    @52
    crp
    wcel
    @94
    @89
    cR
    nnre
    @52
    nnrp
    cR
    @52
    mod0
    syl2an
    syl2anc
    mpbid
    zmulcld
    eqeltrd
    elplyd
    eqeltrd
    wph
    cF
    c0p
    wne
    #
    @14
    wph
    @36
    @95
    wph
    cF
    @35
    @5
    cdif
    wcel
    @36
    @95
    wa
    elqaa.2
    cF
    @35
    c0p
    eldifsn
    sylib
    simprd
    wph
    @10
    c0p
    cF
    c0p
    @10
    c0p
    wceq
    @10
    @9
    cdiv
    cof
    #
    co
    #
    c0p
    @9
    @96
    co
    #
    wceq
    wph
    cF
    c0p
    wceq
    @10
    c0p
    @9
    @96
    oveq1
    wph
    @97
    cF
    @98
    c0p
    wph
    vz
    cc
    @26
    cR
    cdiv
    co
    #
    cmpt
    vz
    cc
    @25
    cmpt
    @97
    cF
    wph
    vz
    cc
    @99
    @25
    @29
    @25
    cR
    wph
    cc
    cc
    @20
    cF
    @39
    ffvelrnda
    @70
    wph
    cR
    cc0
    wne
    @28
    wph
    cR
    @68
    nnne0d
    #
    adantr
    divcan3d
    mpteq2dva
    wph
    vz
    cc
    @26
    cR
    cdiv
    @10
    @9
    cvv
    cvv
    cvv
    @27
    @29
    cR
    @25
    cmul
    ovexd
    @33
    @41
    @34
    offval2
    @40
    3eqtr4d
    wph
    vz
    cc
    cc0
    cR
    cdiv
    co
    #
    cmpt
    vz
    cc
    cc0
    cmpt
    #
    @98
    c0p
    wph
    vz
    cc
    @101
    cc0
    wph
    cR
    @69
    @100
    div0d
    mpteq2dv
    wph
    vz
    cc
    cc0
    cR
    cdiv
    c0p
    @9
    cvv
    cc
    cvv
    @27
    @29
    0cnd
    @33
    c0p
    @102
    wceq
    wph
    c0p
    cc
    cc0
    csn
    cxp
    @102
    df-0p
    vz
    cc
    cc0
    fconstmpt
    eqtri
    a1i
    #
    @34
    offval2
    @103
    3eqtr4d
    eqeq12d
    syl5ib
    necon3d
    mpd
    @10
    @4
    c0p
    eldifsn
    sylanbrc
    wph
    @12
    cR
    cc0
    cmul
    co
    #
    cc0
    wph
    @0
    @12
    @104
    wceq
    elqaa.1
    wph
    cc
    cc
    cR
    cc0
    cmul
    cc
    @9
    cF
    cvv
    cvv
    cA
    cc
    @8
    @9
    wf
    @9
    cc
    wfn
    wph
    cc
    cR
    @32
    fconst
    cc
    @8
    @9
    ffn
    mp1i
    wph
    @37
    cF
    cc
    wfn
    @39
    cc
    cc
    cF
    ffn
    syl
    @27
    @27
    cc
    inidm
    @0
    cA
    @9
    cfv
    cR
    wceq
    wph
    cc
    cR
    cA
    @32
    fvconst2
    adantl
    wph
    cA
    cF
    cfv
    cc0
    wceq
    @0
    elqaa.3
    adantr
    ofval
    mpdan
    wph
    cR
    @69
    mul01d
    eqtrd
    @3
    @13
    vf
    @10
    @6
    @1
    @10
    wceq
    @2
    @12
    cc0
    cA
    @1
    @10
    fveq1
    eqeq1d
    rspcev
    syl2anc
    cA
    vf
    elaa
    sylanbrc
end
