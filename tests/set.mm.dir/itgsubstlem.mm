include "cmul.mm"
include "co.mm"
include "cdit.mm"
include "cioo.mm"
include "citg.mm"
include "ditgpos.mm"
include "cv.mm"
include "cr.mm"
include "cicc.mm"
include "cmpt.mm"
include "cdv.mm"
include "cfv.mm"
include "cmin.mm"
include "cc.mm"
include "ccncf.mm"
include "csb.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "wcel.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "wf.mm"
include "wral.mm"
include "ccom.mm"
include "eqidd.mm"
include "wceq.mm"
include "oveq2.mm"
include "itgeq1.mm"
include "syl.mm"
include "fmptco.mm"
include "eqid.mm"
include "fmptd.mm"
include "wb.mm"
include "ioossicc.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "eliooord.mm"
include "simpld.mm"
include "simprd.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "syl5ss.mm"
include "ioossre.mm"
include "syl6ss.mm"
include "sstrd.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "cdm.mm"
include "sseli.mm"
include "cle.mm"
include "sseldi.mm"
include "rexrd.mm"
include "adantr.mm"
include "w3a.mm"
include "elicc2.mm"
include "biimpa.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sselda.mm"
include "cncff.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "adantlr.mm"
include "cvol.mm"
include "ioombl.mm"
include "cibl.mm"
include "cres.mm"
include "resmptd.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "iblss.mm"
include "itgcl.mm"
include "sylan2.mm"
include "fveq2.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "cbvitg.mm"
include "fvmpt2.mm"
include "itgeq2dv.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "wn.mm"
include "c0.mm"
include "lbicc2.mm"
include "n0i.mm"
include "feq3.mm"
include "syl5ibcom.mm"
include "f00.mm"
include "simprbi.mm"
include "syl6.mm"
include "mtod.mm"
include "ioo0.mm"
include "mtbid.mm"
include "letrid.mm"
include "ord.mm"
include "mpd.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "mpsyl.mm"
include "syl5eqelr.mm"
include "ftc1cn.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "3eqtr3rd.mm"
include "dmeqd.mm"
include "dmmptd.mm"
include "eqtrd.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "cncfco.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "cin.mm"
include "elin.mm"
include "sylib.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "sstri.mm"
include "eqtr3d.mm"
include "syl6eq.mm"
include "csbeq1.mm"
include "dvmptco.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "mulcncf.mm"
include "eqeltrd.mm"
include "cof.mm"
include "fco.mm"
include "feq1d.mm"
include "mpbid.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "cmbf.mm"
include "cabs.mm"
include "wrex.mm"
include "iblmbf.mm"
include "cniccbdd.mm"
include "wi.mm"
include "ssralv.mm"
include "raleqdv.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "syl6rbb.mm"
include "syl5ib.mm"
include "reximdv.mm"
include "bddmulibl.mm"
include "ftc2.mm"
include "nfmpt1.mm"
include "nfov.mm"
include "nffv.mm"
include "fveq1d.mm"
include "cvv.mm"
include "ovex.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "caddc.mm"
include "simp2d.mm"
include "ubicc2.mm"
include "ditgeq2.mm"
include "ditgex.mm"
include "fvmpt.mm"
include "oveq12d.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "ditgsplit.mm"
include "ditgcl.mm"
include "pncan2d.mm"
include "3eqtr3d.mm"
include "eqtr2d.mm"

theorem itgsubstlem
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vv: setvar v
  assume itgsubst.x: |- ( ph -> X e. RR )
  assume itgsubst.y: |- ( ph -> Y e. RR )
  assume itgsubst.le: |- ( ph -> X <_ Y )
  assume itgsubst.z: |- ( ph -> Z e. RR* )
  assume itgsubst.w: |- ( ph -> W e. RR* )
  assume itgsubst.a: |- ( ph -> ( x e. ( X [,] Y ) |-> A ) e. ( ( X [,] Y ) -cn-> ( Z (,) W ) ) )
  assume itgsubst.b: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. ( ( ( X (,) Y ) -cn-> CC ) i^i L^1 ) )
  assume itgsubst.c: |- ( ph -> ( u e. ( Z (,) W ) |-> C ) e. ( ( Z (,) W ) -cn-> CC ) )
  assume itgsubst.da: |- ( ph -> ( RR _D ( x e. ( X [,] Y ) |-> A ) ) = ( x e. ( X (,) Y ) |-> B ) )
  assume itgsubst.e: |- ( u = A -> C = E )
  assume itgsubst.k: |- ( x = X -> A = K )
  assume itgsubst.l: |- ( x = Y -> A = L )
  assume itgsubst.m: |- ( ph -> M e. ( Z (,) W ) )
  assume itgsubst.n: |- ( ph -> N e. ( Z (,) W ) )
  assume itgsubst.cl2: |- ( ( ph /\ x e. ( X [,] Y ) ) -> A e. ( M (,) N ) )

  disjoint E u
  disjoint u x
  disjoint K u
  disjoint K x
  disjoint M u
  disjoint M x
  disjoint ph u
  disjoint ph x
  disjoint X u
  disjoint X x
  disjoint Y u
  disjoint Y x
  disjoint A u
  disjoint C x
  disjoint W u
  disjoint W x
  disjoint L u
  disjoint L x
  disjoint N u
  disjoint N x
  disjoint Z u
  disjoint Z x
  disjoint m n
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint m u
  disjoint E m
  disjoint n u
  disjoint E n
  disjoint u y
  disjoint u z
  disjoint E y
  disjoint E z
  disjoint m x
  disjoint K m
  disjoint n x
  disjoint K n
  disjoint x z
  disjoint K z
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint M t
  disjoint u v
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint x y
  disjoint M y
  disjoint M z
  disjoint m t
  disjoint m v
  disjoint m ph
  disjoint n t
  disjoint n v
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph y
  disjoint ph z
  disjoint X m
  disjoint X n
  disjoint X t
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint Y m
  disjoint Y n
  disjoint Y t
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint A m
  disjoint A n
  disjoint A t
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint W m
  disjoint W n
  disjoint W v
  disjoint W y
  disjoint W z
  disjoint L m
  disjoint L n
  disjoint L z
  disjoint N t
  disjoint N v
  disjoint N y
  disjoint N z
  disjoint Z m
  disjoint Z n
  disjoint Z v
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> S_ [ K -> L ] C _d u = S_ [ X -> Y ] ( E x. B ) _d x )

  proof
    wph
    vx
    cX
    cY
    cE
    cB
    cmul
    co
    #
    cdit
    vx
    cX
    cY
    cioo
    co
    #
    @0
    citg
    #
    vu
    cK
    cL
    cC
    cdit
    #
    wph
    vx
    cX
    cY
    @0
    itgsubst.le
    ditgpos
    wph
    vt
    @1
    vt
    cv
    #
    cr
    vx
    cX
    cY
    cicc
    co
    #
    vu
    cM
    cA
    cioo
    co
    #
    cC
    citg
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    citg
    #
    cY
    @8
    cfv
    #
    cX
    @8
    cfv
    #
    cmin
    co
    #
    @2
    @3
    wph
    vt
    cX
    cY
    @8
    itgsubst.x
    itgsubst.y
    itgsubst.le
    wph
    @9
    vx
    @1
    @0
    cmpt
    #
    @1
    cc
    ccncf
    co
    #
    wph
    @9
    cr
    vx
    @1
    @7
    cmpt
    cdv
    co
    vx
    @1
    vu
    cA
    cC
    csb
    #
    cB
    cmul
    co
    #
    cmpt
    @15
    wph
    vx
    @7
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    @5
    @1
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    wph
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @5
    cr
    wss
    itgsubst.x
    itgsubst.y
    cX
    cY
    iccssre
    syl2anc
    #
    wph
    @7
    cc
    wcel
    #
    vx
    @5
    wph
    @5
    cc
    @8
    wf
    #
    @26
    vx
    @5
    wral
    wph
    @8
    @5
    cc
    ccncf
    co
    #
    wcel
    @27
    wph
    vv
    cM
    cN
    cioo
    co
    #
    vu
    cM
    vv
    cv
    #
    cioo
    co
    #
    cC
    citg
    #
    cmpt
    #
    vx
    @5
    cA
    cmpt
    #
    ccom
    @8
    @28
    wph
    vx
    vv
    @5
    @29
    cA
    @32
    @7
    @34
    @33
    itgsubst.cl2
    wph
    @34
    eqidd
    #
    wph
    @33
    eqidd
    @30
    cA
    wceq
    @31
    @6
    wceq
    @32
    @7
    wceq
    @30
    cA
    cM
    cioo
    oveq2
    vu
    @31
    @6
    cC
    itgeq1
    syl
    #
    fmptco
    wph
    @5
    @29
    cc
    @34
    @33
    wph
    @34
    @5
    @29
    ccncf
    co
    wcel
    #
    @5
    @29
    @34
    wf
    #
    wph
    vx
    @5
    cA
    @29
    @34
    itgsubst.cl2
    @34
    eqid
    #
    fmptd
    #
    wph
    @29
    cc
    wss
    @34
    @5
    cZ
    cW
    cioo
    co
    #
    ccncf
    co
    wcel
    #
    @37
    @38
    wb
    wph
    @29
    @41
    cc
    wph
    @29
    cM
    cN
    cicc
    co
    #
    @41
    cM
    cN
    ioossicc
    #
    wph
    cZ
    cxr
    wcel
    cW
    cxr
    wcel
    cZ
    cM
    clt
    wbr
    #
    cN
    cW
    clt
    wbr
    #
    @43
    @41
    wss
    #
    itgsubst.z
    itgsubst.w
    wph
    @45
    cM
    cW
    clt
    wbr
    #
    wph
    cM
    @41
    wcel
    @45
    @48
    wa
    itgsubst.m
    cM
    cZ
    cW
    eliooord
    syl
    simpld
    wph
    cZ
    cN
    clt
    wbr
    #
    @46
    wph
    cN
    @41
    wcel
    @49
    @46
    wa
    itgsubst.n
    cN
    cZ
    cW
    eliooord
    syl
    simprd
    cZ
    cW
    cM
    cN
    iccssioo
    syl22anc
    #
    syl5ss
    #
    wph
    @41
    cr
    cc
    @41
    cr
    wss
    wph
    cZ
    cW
    ioossre
    #
    a1i
    ax-resscn
    syl6ss
    sstrd
    itgsubst.a
    @5
    @41
    @29
    @34
    cncffvrn
    syl2anc
    mpbird
    wph
    @21
    @29
    cc
    @33
    wf
    @29
    cr
    wss
    cr
    @33
    cdv
    co
    #
    cdm
    #
    @29
    wceq
    @33
    @29
    cc
    ccncf
    co
    #
    wcel
    @22
    wph
    vv
    @29
    @32
    cc
    @33
    @30
    @29
    wcel
    wph
    @30
    @43
    wcel
    #
    @32
    cc
    wcel
    @29
    @43
    @30
    @44
    sseli
    wph
    @56
    wa
    #
    vu
    @31
    cC
    cc
    @57
    vu
    cv
    #
    @31
    wcel
    #
    @58
    @29
    wcel
    #
    cC
    cc
    wcel
    #
    @57
    @31
    @29
    @58
    @57
    cN
    cxr
    wcel
    #
    @30
    cN
    cle
    wbr
    #
    @31
    @29
    wss
    wph
    @62
    @56
    wph
    cN
    wph
    @41
    cr
    cN
    @52
    itgsubst.n
    sseldi
    #
    rexrd
    #
    adantr
    @57
    @30
    cr
    wcel
    #
    cM
    @30
    cle
    wbr
    #
    @63
    wph
    @56
    @66
    @67
    @63
    w3a
    #
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @56
    @68
    wb
    wph
    @41
    cr
    cM
    @52
    itgsubst.m
    sseldi
    #
    @64
    cM
    cN
    @30
    elicc2
    syl2anc
    biimpa
    simp3d
    cM
    @30
    cN
    iooss2
    syl2anc
    #
    sselda
    #
    wph
    @60
    @61
    @56
    wph
    @60
    @58
    @41
    wcel
    #
    @61
    wph
    @29
    @41
    @58
    @51
    sselda
    wph
    @61
    vu
    @41
    wph
    @41
    cc
    vu
    @41
    cC
    cmpt
    #
    wf
    #
    @61
    vu
    @41
    wral
    wph
    @75
    @41
    cc
    ccncf
    co
    wcel
    #
    @76
    itgsubst.c
    @41
    cc
    @75
    cncff
    syl
    #
    vu
    @41
    cc
    cC
    @75
    @75
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    syldan
    #
    adantlr
    #
    syldan
    #
    @57
    vu
    @31
    @29
    cC
    cc
    @72
    @31
    cvol
    cdm
    #
    wcel
    @57
    cM
    @30
    ioombl
    a1i
    @81
    wph
    vu
    @29
    cC
    cmpt
    #
    cibl
    wcel
    @56
    wph
    vu
    @29
    @43
    cC
    cc
    @29
    @43
    wss
    #
    wph
    @44
    a1i
    @29
    @83
    wcel
    wph
    cM
    cN
    ioombl
    a1i
    wph
    @58
    @43
    wcel
    @74
    @61
    wph
    @43
    @41
    @58
    @50
    sselda
    @79
    syldan
    wph
    @69
    @70
    vu
    @43
    cC
    cmpt
    #
    @43
    cc
    ccncf
    co
    #
    wcel
    #
    @86
    cibl
    wcel
    @71
    @64
    wph
    @75
    @43
    cres
    #
    @86
    @87
    wph
    vu
    @41
    @43
    cC
    @50
    resmptd
    wph
    @47
    @77
    @89
    @87
    wcel
    @50
    itgsubst.c
    @41
    cc
    @43
    @75
    rescncf
    sylc
    eqeltrrd
    #
    cM
    cN
    @86
    cniccibl
    syl3anc
    iblss
    #
    adantr
    iblss
    itgcl
    #
    sylan2
    #
    @33
    eqid
    fmptd
    wph
    @29
    @41
    cr
    @51
    @52
    syl6ss
    wph
    @54
    @84
    cdm
    @29
    wph
    @53
    @84
    wph
    cr
    vv
    @43
    vt
    @31
    @4
    @84
    cfv
    #
    citg
    #
    cmpt
    #
    cdv
    co
    cr
    vv
    @43
    @32
    cmpt
    #
    cdv
    co
    @84
    @53
    wph
    @96
    @97
    cr
    cdv
    wph
    vv
    @43
    @95
    @32
    @57
    @95
    vu
    @31
    @58
    @84
    cfv
    #
    citg
    @32
    vt
    vu
    @31
    @94
    @98
    @4
    @58
    @84
    fveq2
    vu
    @29
    cC
    @4
    nffvmpt1
    vt
    @98
    nfcv
    cbvitg
    @57
    vu
    @31
    @98
    cC
    @57
    @59
    wa
    @60
    @61
    @98
    cC
    wceq
    @73
    @82
    vu
    @29
    cC
    cc
    @84
    @84
    eqid
    #
    fvmpt2
    syl2anc
    itgeq2dv
    syl5eq
    mpteq2dva
    oveq2d
    wph
    vv
    vt
    cM
    cN
    @84
    @96
    @96
    eqid
    @71
    @64
    wph
    cN
    cM
    cle
    wbr
    #
    wn
    cM
    cN
    cle
    wbr
    #
    wph
    @29
    c0
    wceq
    #
    @100
    wph
    @102
    @5
    c0
    wceq
    #
    wph
    cX
    @5
    wcel
    #
    @103
    wn
    wph
    cX
    cxr
    wcel
    #
    cY
    cxr
    wcel
    #
    cX
    cY
    cle
    wbr
    #
    @104
    wph
    cX
    itgsubst.x
    rexrd
    #
    wph
    cY
    itgsubst.y
    rexrd
    #
    itgsubst.le
    cX
    cY
    lbicc2
    syl3anc
    #
    @5
    cX
    n0i
    syl
    wph
    @102
    @5
    c0
    @34
    wf
    #
    @103
    wph
    @38
    @102
    @111
    @40
    @29
    c0
    @5
    @34
    feq3
    syl5ibcom
    @111
    @34
    c0
    wceq
    @103
    @5
    @34
    f00
    simprbi
    syl6
    mtod
    wph
    cM
    cxr
    wcel
    #
    @62
    @102
    @100
    wb
    wph
    cM
    @71
    rexrd
    #
    @65
    cM
    cN
    ioo0
    syl2anc
    mtbid
    wph
    @100
    @101
    wph
    cN
    cM
    @64
    @71
    letrid
    ord
    mpd
    #
    wph
    @84
    @86
    @29
    cres
    #
    @55
    @85
    @115
    @84
    wceq
    @44
    vu
    @43
    @29
    cC
    resmpt
    ax-mp
    @85
    wph
    @88
    @115
    @55
    wcel
    @44
    @90
    @43
    cc
    @29
    @86
    rescncf
    mpsyl
    syl5eqelr
    @91
    ftc1cn
    wph
    vv
    @32
    cr
    @19
    @20
    @43
    @29
    @22
    wph
    @43
    @41
    cr
    @50
    @52
    syl6ss
    @92
    @20
    @20
    eqid
    #
    tgioo2
    #
    @116
    wph
    @69
    @70
    @43
    @19
    cnt
    cfv
    #
    cfv
    @29
    wceq
    @71
    @64
    cM
    cN
    iccntr
    syl2anc
    dvmptntr
    3eqtr3rd
    #
    dmeqd
    wph
    vu
    @84
    @29
    cC
    cc
    @99
    @80
    dmmptd
    eqtrd
    @29
    cr
    @33
    dvcn
    syl31anc
    cncfco
    eqeltrrd
    #
    @5
    cc
    @8
    cncff
    syl
    vx
    @5
    cc
    @7
    @8
    @8
    eqid
    fmpt
    sylibr
    r19.21bi
    @117
    @116
    wph
    @23
    @24
    @5
    @118
    cfv
    @1
    wceq
    itgsubst.x
    itgsubst.y
    cX
    cY
    iccntr
    syl2anc
    #
    dvmptntr
    wph
    vx
    vv
    cA
    cB
    @32
    vu
    @30
    cC
    csb
    #
    cr
    cr
    @7
    @17
    cc
    cc
    @1
    @29
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @123
    vx
    cv
    #
    @1
    wcel
    #
    wph
    @124
    @5
    wcel
    #
    cA
    @29
    wcel
    #
    @1
    @5
    @124
    cX
    cY
    ioossicc
    #
    sseli
    #
    itgsubst.cl2
    sylan2
    #
    wph
    cB
    cc
    wcel
    #
    vx
    @1
    wph
    @1
    cc
    vx
    @1
    cB
    cmpt
    #
    wf
    #
    @131
    vx
    @1
    wral
    wph
    @132
    @16
    wcel
    #
    @133
    wph
    @134
    @132
    cibl
    wcel
    #
    wph
    @132
    @16
    cibl
    cin
    wcel
    @134
    @135
    wa
    itgsubst.b
    @132
    @16
    cibl
    elin
    sylib
    #
    simpld
    #
    @1
    cc
    @132
    cncff
    syl
    vx
    @1
    cc
    cB
    @132
    @132
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    @93
    wph
    @122
    cc
    wcel
    #
    vv
    @29
    wph
    @29
    cc
    @84
    wf
    @139
    vv
    @29
    wral
    wph
    vu
    @29
    cC
    cc
    @84
    @80
    @99
    fmptd
    vv
    @29
    cc
    @122
    @84
    vu
    vv
    @29
    cC
    @122
    vv
    cC
    nfcv
    vu
    @30
    cC
    nfcsb1v
    vu
    @30
    cC
    csbeq1a
    cbvmpt
    #
    fmpt
    sylibr
    r19.21bi
    wph
    cr
    @34
    cdv
    co
    cr
    vx
    @1
    cA
    cmpt
    cdv
    co
    @132
    wph
    vx
    cA
    cr
    @19
    @20
    @5
    @1
    @22
    @25
    wph
    @126
    wa
    #
    @41
    cc
    cA
    @41
    cr
    cc
    @52
    ax-resscn
    sstri
    wph
    cA
    @41
    wcel
    #
    vx
    @5
    wph
    @5
    @41
    @34
    wf
    #
    @142
    vx
    @5
    wral
    wph
    @42
    @143
    itgsubst.a
    @5
    @41
    @34
    cncff
    syl
    #
    vx
    @5
    @41
    cA
    @34
    @39
    fmpt
    sylibr
    r19.21bi
    #
    sseldi
    @117
    @116
    @121
    dvmptntr
    itgsubst.da
    eqtr3d
    wph
    @53
    @84
    vv
    @29
    @122
    cmpt
    @119
    @140
    syl6eq
    @36
    vu
    @30
    cA
    cC
    csbeq1
    dvmptco
    wph
    vx
    @1
    @18
    @0
    wph
    @125
    wa
    #
    @17
    cE
    cB
    cmul
    @146
    @127
    @17
    cE
    wceq
    @130
    vu
    cA
    cC
    cE
    @29
    @127
    vu
    cE
    nfcvd
    itgsubst.e
    csbiegf
    syl
    oveq1d
    mpteq2dva
    3eqtrd
    #
    wph
    vx
    cE
    cB
    @1
    wph
    vx
    @1
    cE
    cmpt
    #
    vx
    @5
    cE
    cmpt
    #
    @1
    cres
    #
    @16
    @1
    @5
    wss
    #
    @150
    @148
    wceq
    @128
    vx
    @5
    @1
    cE
    resmpt
    ax-mp
    #
    @151
    wph
    @149
    @28
    wcel
    #
    @150
    @16
    wcel
    @128
    wph
    @75
    @34
    ccom
    #
    @149
    @28
    wph
    vx
    vu
    @5
    @41
    cA
    cC
    cE
    @34
    @75
    @145
    @35
    wph
    @75
    eqidd
    itgsubst.e
    fmptco
    #
    wph
    @5
    @41
    cc
    @34
    @75
    itgsubst.a
    itgsubst.c
    cncfco
    eqeltrrd
    #
    @5
    cc
    @1
    @149
    rescncf
    mpsyl
    syl5eqelr
    @137
    mulcncf
    eqeltrd
    wph
    @9
    @148
    @132
    cmul
    cof
    co
    #
    cibl
    wph
    @9
    @15
    @157
    @147
    wph
    vx
    @1
    cE
    cB
    cmul
    @148
    @132
    @83
    cc
    cc
    @1
    @83
    wcel
    wph
    cX
    cY
    ioombl
    a1i
    #
    @125
    wph
    @126
    cE
    cc
    wcel
    #
    @129
    wph
    @159
    vx
    @5
    wph
    @5
    cc
    @149
    wf
    #
    @159
    vx
    @5
    wral
    wph
    @5
    cc
    @154
    wf
    #
    @160
    wph
    @76
    @143
    @161
    @78
    @144
    @5
    @41
    cc
    @75
    @34
    fco
    syl2anc
    wph
    @5
    cc
    @154
    @149
    @155
    feq1d
    mpbid
    vx
    @5
    cc
    cE
    @149
    @149
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    sylan2
    #
    @138
    wph
    @148
    eqidd
    wph
    @132
    eqidd
    offval2
    eqtr4d
    wph
    @148
    cmbf
    wcel
    #
    @135
    vz
    cv
    #
    @148
    cfv
    #
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    @148
    cdm
    #
    wral
    #
    vy
    cr
    wrex
    #
    @157
    cibl
    wcel
    wph
    @148
    cibl
    wcel
    @164
    wph
    vx
    @1
    @5
    cE
    cc
    @151
    wph
    @128
    a1i
    @158
    @162
    wph
    @23
    @24
    @153
    @149
    cibl
    wcel
    itgsubst.x
    itgsubst.y
    @156
    cX
    cY
    @149
    cniccibl
    syl3anc
    iblss
    @148
    iblmbf
    syl
    wph
    @134
    @135
    @136
    simprd
    wph
    @165
    @149
    cfv
    #
    cabs
    cfv
    #
    @168
    cle
    wbr
    #
    vz
    @5
    wral
    #
    vy
    cr
    wrex
    #
    @172
    wph
    @23
    @24
    @153
    @177
    itgsubst.x
    itgsubst.y
    @156
    vy
    vz
    cX
    cY
    @149
    cniccbdd
    syl3anc
    wph
    @176
    @171
    vy
    cr
    @176
    @175
    vz
    @1
    wral
    #
    wph
    @171
    @151
    @176
    @178
    wi
    @128
    @175
    vz
    @1
    @5
    ssralv
    ax-mp
    wph
    @171
    @169
    vz
    @1
    wral
    @178
    wph
    @169
    vz
    @170
    @1
    wph
    vx
    @148
    @1
    cE
    cc
    @148
    eqid
    @163
    dmmptd
    raleqdv
    @169
    @175
    vz
    @1
    @165
    @1
    wcel
    #
    @167
    @174
    @168
    cle
    @179
    @166
    @173
    cabs
    @179
    @166
    @165
    @150
    cfv
    @173
    @165
    @150
    @148
    @152
    fveq1i
    @165
    @1
    @149
    fvres
    syl5eqr
    fveq2d
    breq1d
    ralbiia
    syl6rbb
    syl5ib
    reximdv
    mpd
    vy
    vz
    @148
    @132
    bddmulibl
    syl3anc
    eqeltrd
    @120
    ftc2
    wph
    @11
    vx
    @1
    @124
    @9
    cfv
    #
    citg
    @2
    vt
    vx
    @1
    @10
    @180
    @4
    @124
    @9
    fveq2
    vx
    @4
    @9
    vx
    cr
    @8
    cdv
    vx
    cr
    nfcv
    vx
    cdv
    nfcv
    vx
    @5
    @7
    nfmpt1
    nfov
    vx
    @4
    nfcv
    nffv
    vt
    @180
    nfcv
    cbvitg
    wph
    vx
    @1
    @180
    @0
    wph
    @125
    @180
    @124
    @15
    cfv
    #
    @0
    wph
    @124
    @9
    @15
    @147
    fveq1d
    @125
    @0
    cvv
    wcel
    @181
    @0
    wceq
    cE
    cB
    cmul
    ovex
    vx
    @1
    @0
    cvv
    @15
    @15
    eqid
    fvmpt2
    mpan2
    sylan9eq
    itgeq2dv
    syl5eq
    wph
    @14
    vu
    cM
    cL
    cC
    cdit
    #
    vu
    cM
    cK
    cC
    cdit
    #
    cmin
    co
    @183
    @3
    caddc
    co
    #
    @183
    cmin
    co
    @3
    wph
    @12
    @182
    @13
    @183
    cmin
    wph
    cY
    vx
    @5
    vu
    cM
    cA
    cC
    cdit
    #
    cmpt
    #
    cfv
    #
    @12
    @182
    wph
    cY
    @186
    @8
    wph
    vx
    @5
    @185
    @7
    @141
    vu
    cM
    cA
    cC
    @141
    cA
    cr
    wcel
    #
    cM
    cA
    cle
    wbr
    #
    cA
    cN
    cle
    wbr
    #
    @141
    cA
    @43
    wcel
    #
    @188
    @189
    @190
    w3a
    #
    @141
    @29
    @43
    cA
    @44
    itgsubst.cl2
    sseldi
    #
    wph
    @191
    @192
    wb
    #
    @126
    wph
    @69
    @70
    @194
    @71
    @64
    cM
    cN
    cA
    elicc2
    syl2anc
    adantr
    mpbid
    simp2d
    ditgpos
    mpteq2dva
    #
    fveq1d
    wph
    cY
    @5
    wcel
    #
    @187
    @182
    wceq
    wph
    @105
    @106
    @107
    @196
    @108
    @109
    itgsubst.le
    cX
    cY
    ubicc2
    syl3anc
    #
    vx
    cY
    @185
    @182
    @5
    @186
    @124
    cY
    wceq
    #
    cA
    cL
    wceq
    @185
    @182
    wceq
    itgsubst.l
    vu
    cA
    cL
    cM
    cC
    ditgeq2
    syl
    @186
    eqid
    #
    vu
    cM
    cL
    cC
    ditgex
    fvmpt
    syl
    eqtr3d
    wph
    cX
    @186
    cfv
    #
    @13
    @183
    wph
    cX
    @186
    @8
    @195
    fveq1d
    wph
    @104
    @200
    @183
    wceq
    @110
    vx
    cX
    @185
    @183
    @5
    @186
    @124
    cX
    wceq
    #
    cA
    cK
    wceq
    @185
    @183
    wceq
    itgsubst.k
    vu
    cA
    cK
    cM
    cC
    ditgeq2
    syl
    @199
    vu
    cM
    cK
    cC
    ditgex
    fvmpt
    syl
    eqtr3d
    oveq12d
    wph
    @182
    @184
    @183
    cmin
    wph
    vu
    cM
    cK
    cL
    cC
    cc
    cM
    cN
    @71
    @64
    wph
    @112
    @62
    @101
    cM
    @43
    wcel
    @113
    @65
    @114
    cM
    cN
    lbicc2
    syl3anc
    #
    wph
    @104
    @191
    vx
    @5
    wral
    #
    cK
    @43
    wcel
    #
    @110
    wph
    @191
    vx
    @5
    @193
    ralrimiva
    #
    @191
    @204
    vx
    cX
    @5
    @201
    cA
    cK
    @43
    itgsubst.k
    eleq1d
    rspcv
    sylc
    #
    wph
    @196
    @203
    cL
    @43
    wcel
    #
    @197
    @205
    @191
    @207
    vx
    cY
    @5
    @198
    cA
    cL
    @43
    itgsubst.l
    eleq1d
    rspcv
    sylc
    #
    @80
    @91
    ditgsplit
    oveq1d
    wph
    @183
    @3
    wph
    vu
    cM
    cK
    cC
    cc
    cM
    cN
    @71
    @64
    @202
    @206
    @80
    @91
    ditgcl
    wph
    vu
    cK
    cL
    cC
    cc
    cM
    cN
    @71
    @64
    @206
    @208
    @80
    @91
    ditgcl
    pncan2d
    3eqtrd
    3eqtr3d
    eqtr2d
end
