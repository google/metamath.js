include "ciun.mm"
include "cv.mm"
include "crn.mm"
include "wf1o.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "wf1.mm"
include "wex.mm"
include "cfn.mm"
include "aciunf1.mm"
include "f1f1orn.mm"
include "anim1i.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "adantr.mm"
include "jca.mm"
include "eximi.mm"
include "csb.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvsum.mm"
include "ccnv.mm"
include "csbeq1.mm"
include "wcel.mm"
include "snfi.mm"
include "xpfi.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ssfid.mm"
include "simprl.mm"
include "f1ocnv.mm"
include "adantrlr.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfrn.mm"
include "nff1o.mm"
include "nfral.mm"
include "nfan.mm"
include "nfss.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simplr.mm"
include "simp-4r.mm"
include "simpld.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "eqtr3d.mm"
include "f1ocnvfv1.mm"
include "3eqtr2rd.mm"
include "wfn.mm"
include "wrex.mm"
include "f1ofn.mm"
include "simpllr.mm"
include "fvelrnb.mm"
include "biimpa.mm"
include "r19.29a.mm"
include "sselda.mm"
include "eliun.mm"
include "sylib.mm"
include "r19.29af.mm"
include "cc.mm"
include "wi.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1w.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "cr.mm"
include "adantllr.mm"
include "recnd.mm"
include "biimpi.mm"
include "adantl.mm"
include "chvar.mm"
include "adantlr.mm"
include "fsumf1o.mm"
include "syl5eq.mm"
include "eqcomd.mm"
include "xp2nd.mm"
include "nfel1.mm"
include "rspc.mm"
include "imp.mm"
include "cc0.mm"
include "c1st.mm"
include "xp1st.mm"
include "elsni.mm"
include "simplll.mm"
include "sylan2.mm"
include "nfbr.mm"
include "breq2d.mm"
include "fsumless.mm"
include "eqbrtrrd.mm"
include "a1i.mm"
include "sumeq2sdv.mm"
include "cop.mm"
include "vex.mm"
include "op2ndd.mm"
include "csbeq1d.mm"
include "anasss.mm"
include "fsum2d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "exlimddv.mm"

theorem fsumiunle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  assume fsumiunle.1: |- ( ph -> A e. Fin )
  assume fsumiunle.2: |- ( ( ph /\ x e. A ) -> B e. Fin )
  assume fsumiunle.3: |- ( ( ( ph /\ x e. A ) /\ k e. B ) -> C e. RR )
  assume fsumiunle.4: |- ( ( ( ph /\ x e. A ) /\ k e. B ) -> 0 <_ C )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint C x
  disjoint k ph
  disjoint ph x
  disjoint A f
  disjoint A l
  disjoint A y
  disjoint A z
  disjoint f k
  disjoint f l
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint k l
  disjoint k y
  disjoint k z
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B f
  disjoint B l
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C y
  disjoint C z
  disjoint f ph
  disjoint l ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> sum_ k e. U_ x e. A B C <_ sum_ x e. A sum_ k e. B C )

  proof
    wph
    vx
    cA
    cB
    ciun
    #
    vf
    cv
    #
    crn
    #
    @1
    wf1o
    #
    vl
    cv
    #
    @1
    cfv
    #
    c2nd
    cfv
    #
    @4
    wceq
    #
    vl
    @0
    wral
    #
    wa
    #
    @2
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    wss
    #
    wa
    #
    @0
    cC
    vk
    csu
    #
    cA
    cB
    cC
    vk
    csu
    #
    vx
    csu
    #
    cle
    wbr
    vf
    wph
    @0
    @13
    @1
    wf1
    #
    @8
    wa
    #
    vf
    wex
    @15
    vf
    wex
    wph
    cA
    cB
    vf
    vx
    vl
    cfn
    cfn
    fsumiunle.1
    fsumiunle.2
    aciunf1
    @20
    @15
    vf
    @20
    @9
    @14
    @19
    @3
    @8
    @0
    @13
    @1
    f1f1orn
    anim1i
    @19
    @14
    @8
    @19
    @0
    @13
    @1
    wf
    @14
    @0
    @13
    @1
    f1f
    @0
    @13
    @1
    frn
    syl
    adantr
    jca
    eximi
    syl
    wph
    @15
    wa
    #
    @16
    @13
    vk
    vz
    cv
    #
    c2nd
    cfv
    #
    cC
    csb
    #
    vz
    csu
    #
    @18
    cle
    @21
    @2
    @24
    vz
    csu
    #
    @16
    @25
    cle
    @21
    @16
    @26
    @21
    @16
    @0
    vk
    vy
    cv
    #
    cC
    csb
    #
    vy
    csu
    @26
    @0
    cC
    @28
    vk
    vy
    vk
    @27
    cC
    csbeq1a
    #
    vy
    @0
    nfcv
    vk
    @0
    nfcv
    vy
    cC
    nfcv
    #
    vk
    @27
    cC
    nfcsb1v
    #
    cbvsum
    @21
    @0
    @28
    @2
    @24
    vy
    vz
    @1
    ccnv
    #
    @23
    vk
    @27
    @23
    cC
    csbeq1
    @21
    @13
    @2
    wph
    @13
    cfn
    wcel
    #
    @15
    wph
    cA
    cfn
    wcel
    @12
    cfn
    wcel
    #
    vx
    cA
    wral
    @33
    fsumiunle.1
    wph
    @34
    vx
    cA
    wph
    @10
    cA
    wcel
    #
    wa
    #
    @11
    cfn
    wcel
    cB
    cfn
    wcel
    @34
    @10
    snfi
    fsumiunle.2
    @11
    cB
    xpfi
    sylancr
    ralrimiva
    vx
    cA
    @12
    iunfi
    syl2anc
    adantr
    #
    wph
    @9
    @14
    simprr
    #
    ssfid
    wph
    @3
    @14
    @2
    @0
    @32
    wf1o
    #
    @8
    wph
    @3
    @14
    wa
    wa
    @3
    @39
    wph
    @3
    @14
    simprl
    @0
    @2
    @1
    f1ocnv
    syl
    adantrlr
    @21
    @22
    @2
    wcel
    #
    wa
    #
    @22
    @12
    wcel
    #
    @22
    @32
    cfv
    #
    @23
    wceq
    #
    vx
    cA
    @21
    @40
    vx
    wph
    @15
    vx
    wph
    vx
    nfv
    #
    @9
    @14
    vx
    @3
    @8
    vx
    vx
    @0
    @2
    @1
    vx
    @1
    nfcv
    #
    vx
    cA
    cB
    nfiu1
    #
    vx
    @1
    @46
    nfrn
    nff1o
    @7
    vx
    vl
    @0
    @47
    @7
    vx
    nfv
    nfral
    nfan
    vx
    @2
    @13
    vx
    @2
    nfcv
    vx
    cA
    @12
    nfiu1
    #
    nfss
    nfan
    nfan
    @40
    vx
    nfv
    nfan
    @41
    @35
    wa
    @42
    wa
    #
    vk
    cv
    #
    @1
    cfv
    #
    @22
    wceq
    #
    @44
    vk
    @0
    @49
    @50
    @0
    wcel
    #
    wa
    #
    @52
    wa
    #
    @23
    @50
    @51
    @32
    cfv
    #
    @43
    @55
    @51
    c2nd
    cfv
    #
    @23
    @50
    @55
    @51
    @22
    c2nd
    @54
    @52
    simpr
    #
    fveq2d
    @55
    @53
    @8
    @57
    @50
    wceq
    #
    @49
    @53
    @52
    simplr
    #
    @49
    @8
    @53
    @52
    @49
    @3
    @8
    @49
    @9
    @14
    wph
    @15
    @40
    @35
    @42
    simp-4r
    simpld
    #
    simprd
    ad2antrr
    @7
    @59
    vl
    @50
    @0
    @4
    @50
    wceq
    #
    @6
    @57
    @4
    @50
    @62
    @5
    @51
    c2nd
    @4
    @50
    @1
    fveq2
    fveq2d
    @62
    id
    eqeq12d
    rspcva
    syl2anc
    eqtr3d
    @55
    @3
    @53
    @56
    @50
    wceq
    @49
    @3
    @53
    @52
    @49
    @3
    @8
    @61
    simpld
    #
    ad2antrr
    @60
    @0
    @2
    @50
    @1
    f1ocnvfv1
    syl2anc
    @55
    @51
    @22
    @32
    @58
    fveq2d
    3eqtr2rd
    @49
    @1
    @0
    wfn
    #
    @40
    @52
    vk
    @0
    wrex
    #
    @49
    @3
    @64
    @63
    @0
    @2
    @1
    f1ofn
    syl
    @21
    @40
    @35
    @42
    simpllr
    @64
    @40
    @65
    vk
    @0
    @22
    @1
    fvelrnb
    biimpa
    syl2anc
    r19.29a
    @41
    @22
    @13
    wcel
    #
    @42
    vx
    cA
    wrex
    #
    @21
    @2
    @13
    @22
    @38
    sselda
    vx
    @22
    cA
    @12
    eliun
    #
    sylib
    r19.29af
    wph
    @27
    @0
    wcel
    #
    @28
    cc
    wcel
    #
    @15
    wph
    @53
    wa
    #
    cC
    cc
    wcel
    #
    wi
    wph
    @69
    wa
    #
    @70
    wi
    vk
    vy
    @73
    @70
    vk
    @73
    vk
    nfv
    vk
    @28
    cc
    @31
    vk
    cc
    nfcv
    nfel
    nfim
    @50
    @27
    wceq
    #
    @71
    @73
    @72
    @70
    @74
    @53
    @69
    wph
    vk
    vy
    @0
    eleq1w
    anbi2d
    @74
    cC
    @28
    cc
    @29
    eleq1d
    #
    imbi12d
    @71
    @50
    cB
    wcel
    #
    @72
    vx
    cA
    wph
    @53
    vx
    @45
    vx
    @50
    @0
    vx
    @50
    nfcv
    @47
    nfel
    nfan
    @71
    @35
    wa
    @76
    wa
    cC
    wph
    @35
    @76
    cC
    cr
    wcel
    #
    @53
    fsumiunle.3
    adantllr
    recnd
    @53
    @76
    vx
    cA
    wrex
    #
    wph
    @53
    @78
    vx
    @50
    cA
    cB
    eliun
    biimpi
    adantl
    r19.29af
    chvar
    adantlr
    fsumf1o
    syl5eq
    eqcomd
    @21
    @13
    @24
    @2
    vz
    @37
    wph
    @66
    @24
    cr
    wcel
    #
    @15
    wph
    @66
    wa
    #
    @42
    @79
    vx
    cA
    wph
    @66
    vx
    @45
    vx
    @22
    @13
    vx
    @22
    nfcv
    @48
    nfel
    nfan
    #
    @80
    @35
    wa
    #
    @42
    wa
    #
    @23
    cB
    wcel
    #
    @77
    vk
    cB
    wral
    #
    @79
    @42
    @84
    @82
    @22
    @11
    cB
    xp2nd
    #
    adantl
    #
    @82
    @85
    @42
    wph
    @35
    @85
    @66
    @36
    @77
    vk
    cB
    fsumiunle.3
    ralrimiva
    adantlr
    adantr
    @84
    @85
    @79
    @77
    @79
    vk
    @23
    cB
    vk
    @24
    cr
    vk
    @23
    cC
    nfcsb1v
    #
    nfel1
    @50
    @23
    wceq
    #
    cC
    @24
    cr
    vk
    @23
    cC
    csbeq1a
    #
    eleq1d
    rspc
    imp
    syl2anc
    @66
    @67
    wph
    @66
    @67
    @68
    biimpi
    adantl
    #
    r19.29af
    adantlr
    wph
    @66
    cc0
    @24
    cle
    wbr
    #
    @15
    @80
    @42
    @92
    vx
    cA
    @81
    @83
    @84
    cc0
    cC
    cle
    wbr
    #
    vk
    cB
    wral
    #
    @92
    @87
    @42
    @82
    @22
    c1st
    cfv
    #
    @10
    wceq
    #
    @84
    wa
    #
    @94
    @42
    @96
    @84
    @42
    @95
    @11
    wcel
    @96
    @22
    @11
    cB
    xp1st
    @95
    @10
    elsni
    syl
    @86
    jca
    @82
    @97
    wa
    wph
    @35
    @94
    wph
    @66
    @35
    @97
    simplll
    @80
    @35
    @97
    simplr
    @36
    @93
    vk
    cB
    fsumiunle.4
    ralrimiva
    syl2anc
    sylan2
    @84
    @94
    @92
    @93
    @92
    vk
    @23
    cB
    vk
    cc0
    @24
    cle
    vk
    cc0
    nfcv
    vk
    cle
    nfcv
    @88
    nfbr
    @89
    cC
    @24
    cc0
    cle
    @90
    breq2d
    rspc
    imp
    syl2anc
    @91
    r19.29af
    adantlr
    @38
    fsumless
    eqbrtrrd
    wph
    @18
    @25
    wceq
    @15
    wph
    @18
    cA
    cB
    @28
    vy
    csu
    #
    vx
    csu
    @25
    wph
    cA
    @17
    @98
    vx
    @17
    @98
    wceq
    wph
    cB
    cC
    @28
    vk
    vy
    @29
    vy
    cB
    nfcv
    vk
    cB
    nfcv
    @30
    @31
    cbvsum
    a1i
    sumeq2sdv
    wph
    vz
    cA
    cB
    @28
    @24
    vx
    vy
    @22
    @10
    @27
    cop
    wceq
    #
    @28
    @24
    @99
    vk
    @27
    @23
    cC
    @99
    @23
    @27
    @10
    @27
    @22
    vx
    vex
    vy
    vex
    op2ndd
    eqcomd
    csbeq1d
    eqcomd
    fsumiunle.1
    fsumiunle.2
    wph
    @35
    @27
    cB
    wcel
    #
    @70
    @36
    @76
    wa
    #
    @72
    wi
    @36
    @100
    wa
    #
    @70
    wi
    vk
    vy
    @102
    @70
    vk
    @102
    vk
    nfv
    vk
    @28
    cc
    @31
    nfel1
    nfim
    @74
    @101
    @102
    @72
    @70
    @74
    @76
    @100
    @36
    vk
    vy
    cB
    eleq1w
    anbi2d
    @75
    imbi12d
    @101
    cC
    fsumiunle.3
    recnd
    chvar
    anasss
    fsum2d
    eqtrd
    adantr
    breqtrrd
    exlimddv
end
