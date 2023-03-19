include "csu.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cexp.mm"
include "cfv.mm"
include "csb.mm"
include "cmpt.mm"
include "crn.mm"
include "cop.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "co.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "syl.mm"
include "csbied.mm"
include "wcel.mm"
include "cfn.mm"
include "wf1.mm"
include "adantr.mm"
include "cprime.mm"
include "cn.mm"
include "biimpd.mm"
include "impl.mm"
include "simprd.mm"
include "ex.mm"
include "weq.mm"
include "wb.mm"
include "simpld.mm"
include "adantrr.mm"
include "ssrdv.mm"
include "sselda.mm"
include "adantrl.mm"
include "eqid.mm"
include "prmexpb.mm"
include "baibd.mm"
include "mpan2.mm"
include "syl22anc.mm"
include "dom2lem.mm"
include "f1fi.mm"
include "syl2anc.mm"
include "cc.mm"
include "wral.mm"
include "simplbda.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fsum2d.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "csbeq1.mm"
include "snfi.mm"
include "xpfi.mm"
include "sylancr.mm"
include "iunfi.mm"
include "wf1o.mm"
include "fvex.mm"
include "2a1i.mm"
include "wex.mm"
include "eliunxp.mm"
include "simprbda.mm"
include "opelxp.mm"
include "sylibr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "impancom.mm"
include "expimpd.mm"
include "exlimdvv.mm"
include "syl5bi.mm"
include "sseld.mm"
include "anim12d.mm"
include "c1st.mm"
include "c2nd.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "eqeqan12d.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "jca.mm"
include "an4s.mm"
include "syl2an.mm"
include "xpopth.mm"
include "3bitrd.mm"
include "syl6.mm"
include "f1f1orn.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wf.mm"
include "wss.mm"
include "imp.mm"
include "fmptd.mm"
include "frn.mm"
include "nfel1.mm"
include "rspc.mm"
include "mpan9.mm"
include "syldan.mm"
include "fsumf1o.mm"
include "syl5eq.mm"
include "cdif.mm"
include "cc0.mm"
include "wn.mm"
include "eldif.mm"
include "cvma.mm"
include "wrex.mm"
include "wne.mm"
include "elrnmpti.mm"
include "rexiunxp.mm"
include "bitri.mm"
include "simpr.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "rbaibd.mm"
include "adantlr.mm"
include "pm5.32da.mm"
include "ancom.mm"
include "3bitr4g.mm"
include "2exbidv.mm"
include "r2ex.mm"
include "isppw2.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "necon2bbid.mm"
include "sylbird.mm"
include "fsumss.mm"
include "3eqtr2rd.mm"

theorem fsumvma
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let vk: setvar k
  let cK: class K
  let vp: setvar p
  let va: setvar a
  let vz: setvar z
  let vb: setvar b
  let vy: setvar y
  assume fsumvma.1: |- ( x = ( p ^ k ) -> B = C )
  assume fsumvma.2: |- ( ph -> A e. Fin )
  assume fsumvma.3: |- ( ph -> A C_ NN )
  assume fsumvma.4: |- ( ph -> P e. Fin )
  assume fsumvma.5: |- ( ph -> ( ( p e. P /\ k e. K ) <-> ( ( p e. Prime /\ k e. NN ) /\ ( p ^ k ) e. A ) ) )
  assume fsumvma.6: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume fsumvma.7: |- ( ( ph /\ ( x e. A /\ ( Lam ` x ) = 0 ) ) -> B = 0 )

  disjoint k p
  disjoint k x
  disjoint A k
  disjoint p x
  disjoint A p
  disjoint A x
  disjoint C x
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint p ph
  disjoint ph x
  disjoint B k
  disjoint B p
  disjoint P k
  disjoint P p
  disjoint P x
  disjoint a k
  disjoint a p
  disjoint a x
  disjoint a z
  disjoint A a
  disjoint k z
  disjoint p z
  disjoint x z
  disjoint A z
  disjoint C z
  disjoint a b
  disjoint a y
  disjoint K a
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint K b
  disjoint k y
  disjoint x y
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint a ph
  disjoint b p
  disjoint b ph
  disjoint p y
  disjoint ph y
  disjoint ph z
  disjoint B y
  disjoint B z
  disjoint P a
  disjoint P b
  disjoint P y
  disjoint P z
  assert |- ( ph -> sum_ x e. A B = sum_ p e. P sum_ k e. K C )

  proof
    wph
    cP
    cK
    cC
    vk
    csu
    vp
    csu
    vp
    cP
    vp
    cv
    #
    csn
    #
    cK
    cxp
    #
    ciun
    #
    vx
    vz
    cv
    #
    cexp
    cfv
    #
    cB
    csb
    #
    vz
    csu
    #
    va
    @3
    va
    cv
    #
    cexp
    cfv
    #
    cmpt
    #
    crn
    #
    cB
    vx
    csu
    #
    cA
    cB
    vx
    csu
    wph
    vz
    cP
    cK
    cC
    @6
    vp
    vk
    @4
    @0
    vk
    cv
    #
    cop
    #
    wceq
    #
    vx
    @5
    cB
    cC
    cvv
    @15
    @4
    cexp
    fvexd
    @15
    vx
    cv
    #
    @5
    wceq
    #
    wa
    @16
    @0
    @13
    cexp
    co
    #
    wceq
    #
    cB
    cC
    wceq
    @15
    @17
    @19
    @15
    @5
    @18
    @16
    @15
    @5
    @14
    cexp
    cfv
    #
    @18
    @4
    @14
    cexp
    fveq2
    @0
    @13
    cexp
    df-ov
    #
    syl6eqr
    eqeq2d
    biimpa
    fsumvma.1
    syl
    csbied
    fsumvma.4
    wph
    @0
    cP
    wcel
    #
    wa
    #
    cA
    cfn
    wcel
    #
    cK
    cA
    vk
    cK
    @18
    cmpt
    #
    wf1
    cK
    cfn
    wcel
    #
    wph
    @24
    @22
    fsumvma.2
    adantr
    @23
    vk
    vz
    cK
    cA
    @18
    @0
    @4
    cexp
    co
    #
    @23
    @13
    cK
    wcel
    #
    @18
    cA
    wcel
    #
    @23
    @28
    wa
    #
    @0
    cprime
    wcel
    #
    @13
    cn
    wcel
    #
    wa
    #
    @29
    wph
    @22
    @28
    @33
    @29
    wa
    #
    wph
    @22
    @28
    wa
    #
    @34
    fsumvma.5
    biimpd
    impl
    #
    simprd
    ex
    @23
    @28
    @4
    cK
    wcel
    #
    wa
    #
    @18
    @27
    wceq
    #
    vk
    vz
    weq
    #
    wb
    #
    @23
    @38
    wa
    @31
    @31
    @32
    @4
    cn
    wcel
    #
    @41
    @23
    @28
    @31
    @37
    @30
    @31
    @32
    @30
    @33
    @29
    @36
    simpld
    #
    simpld
    adantrr
    #
    @44
    @23
    @28
    @32
    @37
    @30
    @31
    @32
    @43
    simprd
    #
    adantrr
    @23
    @37
    @42
    @28
    @23
    cK
    cn
    @4
    @23
    vk
    cK
    cn
    @23
    @28
    @32
    @45
    ex
    ssrdv
    sselda
    adantrl
    @31
    @31
    wa
    @32
    @42
    wa
    wa
    #
    vp
    vp
    weq
    #
    @41
    @0
    eqid
    @46
    @39
    @47
    @40
    @0
    @0
    @13
    @4
    prmexpb
    baibd
    mpan2
    syl22anc
    ex
    dom2lem
    cK
    cA
    @25
    f1fi
    syl2anc
    #
    wph
    @35
    wa
    #
    @29
    cB
    cc
    wcel
    #
    vx
    cA
    wral
    #
    cC
    cc
    wcel
    #
    wph
    @35
    @33
    @29
    fsumvma.5
    simplbda
    #
    wph
    @51
    @35
    wph
    @50
    vx
    cA
    fsumvma.6
    ralrimiva
    #
    adantr
    @50
    @52
    vx
    @18
    cA
    @19
    cB
    cC
    cc
    fsumvma.1
    eleq1d
    rspcv
    sylc
    fsum2d
    wph
    @12
    @11
    vx
    vy
    cv
    #
    cB
    csb
    #
    vy
    csu
    @7
    @11
    cB
    @56
    vx
    vy
    vy
    cB
    nfcv
    vx
    @55
    cB
    nfcsb1v
    #
    vx
    @55
    cB
    csbeq1a
    #
    cbvsumi
    wph
    @11
    @56
    @3
    @6
    vy
    vz
    @10
    @5
    vx
    @55
    @5
    cB
    csbeq1
    wph
    cP
    cfn
    wcel
    @2
    cfn
    wcel
    #
    vp
    cP
    wral
    @3
    cfn
    wcel
    fsumvma.4
    wph
    @59
    vp
    cP
    @23
    @1
    cfn
    wcel
    @26
    @59
    @0
    snfi
    @48
    @1
    cK
    xpfi
    sylancr
    ralrimiva
    vp
    cP
    @2
    iunfi
    syl2anc
    wph
    @3
    cvv
    @10
    wf1
    @3
    @11
    @10
    wf1o
    wph
    va
    vb
    @3
    cvv
    @9
    vb
    cv
    #
    cexp
    cfv
    #
    @9
    cvv
    wcel
    wph
    @8
    @3
    wcel
    #
    @8
    cexp
    fvex
    #
    2a1i
    wph
    @62
    @60
    @3
    wcel
    #
    wa
    @8
    cprime
    cn
    cxp
    #
    wcel
    #
    @60
    @65
    wcel
    #
    wa
    #
    @9
    @61
    wceq
    #
    va
    vb
    weq
    #
    wb
    wph
    @62
    @66
    @64
    @67
    @62
    @8
    @14
    wceq
    #
    @35
    wa
    #
    vk
    wex
    vp
    wex
    #
    wph
    @66
    vp
    vk
    cP
    cK
    @8
    eliunxp
    #
    wph
    @72
    @66
    vp
    vk
    wph
    @71
    @35
    @66
    wph
    @35
    @71
    @66
    @49
    @66
    @71
    @14
    @65
    wcel
    #
    @49
    @33
    @75
    wph
    @35
    @33
    @29
    fsumvma.5
    simprbda
    @0
    @13
    cprime
    cn
    opelxp
    sylibr
    @8
    @14
    @65
    eleq1
    syl5ibrcom
    impancom
    expimpd
    exlimdvv
    syl5bi
    #
    wph
    @3
    @65
    @60
    wph
    va
    @3
    @65
    @76
    ssrdv
    sseld
    anim12d
    @68
    @69
    @8
    c1st
    cfv
    #
    @8
    c2nd
    cfv
    #
    cexp
    co
    #
    @60
    c1st
    cfv
    #
    @60
    c2nd
    cfv
    #
    cexp
    co
    #
    wceq
    #
    @77
    @80
    wceq
    @78
    @81
    wceq
    wa
    #
    @70
    @66
    @67
    @9
    @79
    @61
    @82
    @66
    @9
    @77
    @78
    cop
    #
    cexp
    cfv
    @79
    @66
    @8
    @85
    cexp
    @8
    cprime
    cn
    1st2nd2
    fveq2d
    @77
    @78
    cexp
    df-ov
    syl6eqr
    @67
    @61
    @80
    @81
    cop
    #
    cexp
    cfv
    @82
    @67
    @60
    @86
    cexp
    @60
    cprime
    cn
    1st2nd2
    fveq2d
    @80
    @81
    cexp
    df-ov
    syl6eqr
    eqeqan12d
    @66
    @77
    cprime
    wcel
    #
    @78
    cn
    wcel
    #
    wa
    @80
    cprime
    wcel
    #
    @81
    cn
    wcel
    #
    wa
    @83
    @84
    wb
    #
    @67
    @66
    @87
    @88
    @8
    cprime
    cn
    xp1st
    @8
    cprime
    cn
    xp2nd
    jca
    @67
    @89
    @90
    @60
    cprime
    cn
    xp1st
    @60
    cprime
    cn
    xp2nd
    jca
    @87
    @89
    @88
    @90
    @91
    @77
    @80
    @78
    @81
    prmexpb
    an4s
    syl2an
    @8
    @60
    cprime
    cn
    cprime
    cn
    xpopth
    3bitrd
    syl6
    dom2lem
    @3
    cvv
    @10
    f1f1orn
    syl
    @4
    @3
    wcel
    @4
    @10
    cfv
    @5
    wceq
    wph
    va
    @4
    @9
    @5
    @3
    @10
    @8
    @4
    cexp
    fveq2
    @10
    eqid
    #
    @4
    cexp
    fvex
    fvmpt
    adantl
    wph
    @55
    @11
    wcel
    @55
    cA
    wcel
    #
    @56
    cc
    wcel
    #
    wph
    @11
    cA
    @55
    wph
    @3
    cA
    @10
    wf
    @11
    cA
    wss
    wph
    va
    @3
    @9
    cA
    @10
    wph
    @62
    @9
    cA
    wcel
    #
    @62
    @73
    wph
    @95
    @74
    wph
    @72
    @95
    vp
    vk
    wph
    @71
    @35
    @95
    wph
    @35
    @71
    @95
    @49
    @95
    @71
    @29
    @53
    @71
    @9
    @18
    cA
    @71
    @9
    @20
    @18
    @8
    @14
    cexp
    fveq2
    @21
    syl6eqr
    #
    eleq1d
    syl5ibrcom
    impancom
    expimpd
    exlimdvv
    syl5bi
    imp
    @92
    fmptd
    @3
    cA
    @10
    frn
    syl
    #
    sselda
    wph
    @51
    @93
    @94
    @54
    @50
    @94
    vx
    @55
    cA
    vx
    @56
    cc
    @57
    nfel1
    vx
    vy
    weq
    cB
    @56
    cc
    @58
    eleq1d
    rspc
    mpan9
    syldan
    fsumf1o
    syl5eq
    wph
    @11
    cA
    cB
    vx
    @97
    wph
    @16
    @11
    wcel
    #
    @16
    cA
    wcel
    #
    @50
    wph
    @11
    cA
    @16
    @97
    sselda
    fsumvma.6
    syldan
    wph
    @16
    cA
    @11
    cdif
    wcel
    #
    cB
    cc0
    wceq
    #
    @100
    @99
    @98
    wn
    #
    wa
    #
    wph
    @101
    @16
    cA
    @11
    eldif
    wph
    @103
    @99
    @16
    cvma
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @101
    wph
    @99
    @105
    @102
    wph
    @99
    wa
    #
    @98
    @104
    cc0
    @98
    @19
    vk
    cK
    wrex
    vp
    cP
    wrex
    #
    @107
    @104
    cc0
    wne
    #
    @98
    @16
    @9
    wceq
    #
    va
    @3
    wrex
    @108
    va
    @3
    @9
    @16
    @10
    @92
    @63
    elrnmpti
    @110
    @19
    va
    vp
    vk
    cP
    cK
    @71
    @9
    @18
    @16
    @96
    eqeq2d
    rexiunxp
    bitri
    @107
    @108
    @19
    vk
    cn
    wrex
    vp
    cprime
    wrex
    #
    @109
    @107
    @35
    @19
    wa
    #
    vk
    wex
    vp
    wex
    @33
    @19
    wa
    #
    vk
    wex
    vp
    wex
    @108
    @111
    @107
    @112
    @113
    vp
    vk
    @107
    @19
    @35
    wa
    @19
    @33
    wa
    @112
    @113
    @107
    @19
    @35
    @33
    @107
    @19
    @29
    @35
    @33
    wb
    #
    @107
    @19
    wa
    @16
    @18
    cA
    @107
    @19
    simpr
    wph
    @99
    @19
    simplr
    eqeltrrd
    wph
    @29
    @114
    @99
    wph
    @35
    @33
    @29
    fsumvma.5
    rbaibd
    adantlr
    syldan
    pm5.32da
    @35
    @19
    ancom
    @33
    @19
    ancom
    3bitr4g
    2exbidv
    @19
    vp
    vk
    cP
    cK
    r2ex
    @19
    vp
    vk
    cprime
    cn
    r2ex
    3bitr4g
    @107
    @16
    cn
    wcel
    @109
    @111
    wb
    wph
    cA
    cn
    @16
    fsumvma.3
    sselda
    @16
    vk
    vp
    isppw2
    syl
    bitr4d
    syl5bb
    necon2bbid
    pm5.32da
    wph
    @106
    @101
    fsumvma.7
    ex
    sylbird
    syl5bi
    imp
    fsumvma.2
    fsumss
    3eqtr2rd
end
