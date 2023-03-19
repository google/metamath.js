include "cuni.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "iccssxr.mm"
include "cpw.mm"
include "elpwincl1.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "elpwdifcl.mm"
include "xaddcld.mm"
include "adantr.mm"
include "pnfge.mm"
include "syl.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "wne.mm"
include "c0.mm"
include "clt.mm"
include "wn.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "fveq2d.mm"
include "difeq2d.mm"
include "dif0.mm"
include "oveq12d.mm"
include "adantl.mm"
include "oveq1d.mm"
include "xaddid2.mm"
include "3eqtrd.mm"
include "wb.mm"
include "eqeltrd.mm"
include "xeqlelt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "adantlr.mm"
include "cn.mm"
include "cv.mm"
include "wfo.mm"
include "csdm.mm"
include "cdom.mm"
include "wex.mm"
include "ccarsg.mm"
include "wss.mm"
include "cvv.mm"
include "fvex.mm"
include "ssex.mm"
include "0sdomg.mm"
include "3syl.mm"
include "biimpar.mm"
include "com.mm"
include "cen.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "sylancl.mm"
include "ad2antrr.mm"
include "fodomr.mm"
include "c1.mm"
include "cfzo.mm"
include "ciun.mm"
include "fveq2.mm"
include "iundisj.mm"
include "crn.mm"
include "wfn.mm"
include "fofn.mm"
include "fniunfv.mm"
include "forn.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "ad3antrrr.mm"
include "wf.mm"
include "cesum.mm"
include "3adant1r.mm"
include "wdisj.mm"
include "iundisj2.mm"
include "a1i.mm"
include "ad4antr.mm"
include "fof.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "carsgsigalem.mm"
include "wrex.mm"
include "cab.mm"
include "wral.mm"
include "ad3antlr.mm"
include "fzossnn.mm"
include "sselda.mm"
include "ralrimiva.mm"
include "dfiun2g.mm"
include "cfn.mm"
include "cmpt.mm"
include "eqid.mm"
include "rnmpt.mm"
include "fzofi.mm"
include "mptfi.mm"
include "rnfi.mm"
include "mp2b.mm"
include "eqeltrri.mm"
include "rnmptss.mm"
include "syl5eqssr.mm"
include "fiunelcarsg.mm"
include "difelcarsg2.mm"
include "simpllr.mm"
include "carsgclctunlem2.mm"
include "eqbrtrrd.mm"
include "exlimddv.mm"
include "pm2.61dane.mm"

theorem carsgclctunlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cE: class E
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let vb: setvar b
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let vg: setvar g
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume carsgsiga.3: |- ( ( ph /\ x C_ y /\ y e. ~P O ) -> ( M ` x ) <_ ( M ` y ) )
  assume carsgclctun.1: |- ( ph -> A ~<_ _om )
  assume carsgclctun.2: |- ( ph -> A C_ ( toCaraSiga ` M ) )
  assume carsgclctunlem3.1: |- ( ph -> E e. ~P O )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint E x
  disjoint E y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint M b
  disjoint M f
  disjoint O f
  disjoint b ph
  disjoint f ph
  disjoint f k
  disjoint f n
  disjoint f z
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint A g
  disjoint A k
  disjoint A n
  disjoint e g
  disjoint e k
  disjoint e n
  disjoint f g
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint E f
  disjoint E g
  disjoint E k
  disjoint E n
  disjoint M g
  disjoint M k
  disjoint M n
  disjoint O g
  disjoint O n
  disjoint g ph
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> ( ( M ` ( E i^i U. A ) ) +e ( M ` ( E \ U. A ) ) ) <_ ( M ` E ) )

  proof
    wph
    cE
    cA
    cuni
    #
    cin
    #
    cM
    cfv
    #
    cE
    @0
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    cE
    cM
    cfv
    #
    cle
    wbr
    #
    @6
    cpnf
    wph
    @6
    cpnf
    wceq
    #
    wa
    #
    @5
    cpnf
    @6
    cle
    @9
    @5
    cxr
    wcel
    #
    @5
    cpnf
    cle
    wbr
    wph
    @10
    @8
    wph
    @2
    @4
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @2
    cc0
    cpnf
    iccssxr
    #
    wph
    cO
    cpw
    #
    @11
    @1
    cM
    carsgval.2
    wph
    cE
    @0
    cO
    carsgclctunlem3.1
    elpwincl1
    ffvelrnd
    sseldi
    wph
    @11
    cxr
    @4
    @12
    wph
    @13
    @11
    @3
    cM
    carsgval.2
    wph
    cE
    @0
    cO
    carsgclctunlem3.1
    elpwdifcl
    ffvelrnd
    sseldi
    xaddcld
    adantr
    @5
    pnfge
    syl
    wph
    @8
    simpr
    breqtrrd
    wph
    @6
    cpnf
    wne
    #
    wa
    #
    @7
    cA
    c0
    wph
    cA
    c0
    wceq
    #
    @7
    @14
    wph
    @16
    wa
    #
    @7
    @5
    @6
    clt
    wbr
    wn
    #
    @17
    @5
    @6
    wceq
    #
    @7
    @18
    wa
    #
    @17
    @5
    c0
    cM
    cfv
    #
    @6
    cxad
    co
    #
    cc0
    @6
    cxad
    co
    #
    @6
    @16
    @5
    @22
    wceq
    wph
    @16
    @2
    @21
    @4
    @6
    cxad
    @16
    @1
    c0
    cM
    @16
    @1
    cE
    c0
    cin
    c0
    @16
    @0
    c0
    cE
    @16
    @0
    c0
    cuni
    c0
    cA
    c0
    unieq
    uni0
    syl6eq
    #
    ineq2d
    cE
    in0
    syl6eq
    fveq2d
    @16
    @3
    cE
    cM
    @16
    @3
    cE
    c0
    cdif
    cE
    @16
    @0
    c0
    cE
    @24
    difeq2d
    cE
    dif0
    syl6eq
    fveq2d
    oveq12d
    adantl
    @17
    @21
    cc0
    @6
    cxad
    wph
    @21
    cc0
    wceq
    #
    @16
    carsgsiga.1
    adantr
    oveq1d
    @17
    @6
    cxr
    wcel
    #
    @23
    @6
    wceq
    wph
    @26
    @16
    wph
    @11
    cxr
    @6
    @12
    wph
    @13
    @11
    cE
    cM
    carsgval.2
    carsgclctunlem3.1
    ffvelrnd
    sseldi
    adantr
    #
    @6
    xaddid2
    syl
    3eqtrd
    #
    @17
    @10
    @26
    @19
    @20
    wb
    @17
    @5
    @6
    cxr
    @28
    @27
    eqeltrd
    @27
    @5
    @6
    xeqlelt
    syl2anc
    mpbid
    simpld
    adantlr
    @15
    cA
    c0
    wne
    #
    wa
    #
    cn
    cA
    vf
    cv
    #
    wfo
    #
    @7
    vf
    @30
    c0
    cA
    csdm
    wbr
    #
    cA
    cn
    cdom
    wbr
    #
    @32
    vf
    wex
    wph
    @29
    @33
    @14
    wph
    @33
    @29
    wph
    cA
    cM
    ccarsg
    cfv
    #
    wss
    #
    cA
    cvv
    wcel
    @33
    @29
    wb
    carsgclctun.2
    cA
    @35
    cM
    ccarsg
    fvex
    ssex
    cA
    cvv
    0sdomg
    3syl
    biimpar
    adantlr
    wph
    @34
    @14
    @29
    wph
    cA
    com
    cdom
    wbr
    com
    cn
    cen
    wbr
    @34
    carsgclctun.1
    cn
    com
    nnenom
    ensymi
    cA
    com
    cn
    domentr
    sylancl
    ad2antrr
    cn
    cA
    vf
    fodomr
    syl2anc
    @30
    @32
    wa
    #
    cE
    vn
    cn
    vn
    cv
    #
    @31
    cfv
    #
    vk
    c1
    @38
    cfzo
    co
    #
    vk
    cv
    #
    @31
    cfv
    #
    ciun
    #
    cdif
    #
    ciun
    #
    cin
    #
    cM
    cfv
    #
    cE
    @45
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    @5
    @6
    cle
    @37
    @47
    @2
    @49
    @4
    cxad
    @37
    @46
    @1
    cM
    @37
    @45
    @0
    cE
    @37
    @45
    vn
    cn
    @39
    ciun
    #
    @0
    @39
    @42
    vk
    vn
    @38
    @41
    @31
    fveq2
    #
    iundisj
    @32
    @50
    @0
    wceq
    @30
    @32
    @50
    @31
    crn
    #
    cuni
    #
    @0
    @32
    @31
    cn
    wfn
    @50
    @53
    wceq
    cn
    cA
    @31
    fofn
    vn
    cn
    @31
    fniunfv
    syl
    @32
    @52
    cA
    cn
    cA
    @31
    forn
    unieqd
    eqtrd
    adantl
    syl5eqr
    #
    ineq2d
    fveq2d
    @37
    @48
    @3
    cM
    @37
    @45
    @0
    cE
    @54
    difeq2d
    fveq2d
    oveq12d
    @37
    vx
    vy
    @44
    vn
    cE
    cM
    cO
    cV
    wph
    cO
    cV
    wcel
    #
    @14
    @29
    @32
    carsgval.1
    ad3antrrr
    #
    wph
    @13
    @11
    cM
    wf
    #
    @14
    @29
    @32
    carsgval.2
    ad3antrrr
    #
    wph
    @25
    @14
    @29
    @32
    carsgsiga.1
    ad3antrrr
    #
    @30
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @60
    @13
    wss
    #
    @60
    cuni
    cM
    cfv
    @60
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    cle
    wbr
    #
    @32
    @15
    @61
    @62
    @65
    @29
    wph
    @61
    @62
    @65
    @14
    carsgsiga.2
    3adant1r
    3adant1r
    3adant1r
    #
    @30
    @60
    @63
    wss
    #
    @63
    @13
    wcel
    #
    @60
    cM
    cfv
    @64
    cle
    wbr
    #
    @32
    @15
    @67
    @68
    @69
    @29
    wph
    @67
    @68
    @69
    @14
    carsgsiga.3
    3adant1r
    3adant1r
    3adant1r
    vn
    cn
    @44
    wdisj
    @37
    @39
    @42
    vk
    vn
    @51
    iundisj2
    a1i
    @37
    @38
    cn
    wcel
    #
    wa
    #
    @39
    @43
    cM
    cO
    cV
    ve
    vg
    @37
    @55
    @70
    @56
    adantr
    #
    @37
    @57
    @70
    @58
    adantr
    #
    @71
    cA
    @35
    @39
    wph
    @36
    @14
    @29
    @32
    @70
    carsgclctun.2
    ad4antr
    #
    @71
    cn
    cA
    @38
    @31
    @32
    cn
    cA
    @31
    wf
    #
    @30
    @70
    cn
    cA
    @31
    fof
    #
    ad2antlr
    @37
    @70
    simpr
    ffvelrnd
    sseldd
    @71
    vx
    vy
    ve
    vg
    cM
    cO
    cV
    @72
    @73
    @37
    @25
    @70
    @59
    adantr
    #
    @37
    @61
    @62
    @65
    @70
    @66
    3adant1r
    #
    carsgsigalem
    @71
    @43
    vz
    cv
    @42
    wceq
    vk
    @40
    wrex
    vz
    cab
    #
    cuni
    #
    @35
    @71
    @42
    cA
    wcel
    #
    vk
    @40
    wral
    @43
    @80
    wceq
    @71
    @81
    vk
    @40
    @71
    @41
    @40
    wcel
    #
    wa
    #
    cn
    cA
    @41
    @31
    @32
    @75
    @30
    @70
    @82
    @76
    ad3antlr
    @71
    @40
    cn
    @41
    @40
    cn
    wss
    @71
    @38
    fzossnn
    a1i
    sselda
    ffvelrnd
    #
    ralrimiva
    vk
    vz
    @40
    @42
    cA
    dfiun2g
    syl
    @71
    vx
    vy
    @79
    cM
    cO
    cV
    @72
    @73
    @77
    @78
    @79
    cfn
    wcel
    @71
    vk
    @40
    @42
    cmpt
    #
    crn
    #
    @79
    cfn
    vk
    vz
    @40
    @42
    @85
    @85
    eqid
    #
    rnmpt
    #
    @40
    cfn
    wcel
    @85
    cfn
    wcel
    @86
    cfn
    wcel
    c1
    @38
    fzofi
    vk
    @40
    @42
    mptfi
    @85
    rnfi
    mp2b
    eqeltrri
    a1i
    @71
    @79
    @86
    @35
    @88
    @71
    @42
    @35
    wcel
    #
    vk
    @40
    wral
    @86
    @35
    wss
    @71
    @89
    vk
    @40
    @83
    cA
    @35
    @42
    @71
    @36
    @82
    @74
    adantr
    @84
    sseldd
    ralrimiva
    vk
    @40
    @42
    @35
    @85
    @87
    rnmptss
    syl
    syl5eqssr
    fiunelcarsg
    eqeltrd
    difelcarsg2
    wph
    cE
    @13
    wcel
    @14
    @29
    @32
    carsgclctunlem3.1
    ad3antrrr
    wph
    @14
    @29
    @32
    simpllr
    carsgclctunlem2
    eqbrtrrd
    exlimddv
    pm2.61dane
    pm2.61dane
end
