include "ccmn.mm"
include "wcel.mm"
include "ctmd.mm"
include "cfn.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cgsu.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "cfv.mm"
include "ccn.mm"
include "cpw.mm"
include "cxko.mm"
include "wa.mm"
include "wi.mm"
include "c0.mm"
include "cun.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq1d.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "imbi2d.mm"
include "c0g.mm"
include "wfn.mm"
include "elmapfn.mm"
include "fn0.mm"
include "sylib.mm"
include "oveq2d.mm"
include "eqid.mm"
include "gsum0.mm"
include "mpteq2ia.mm"
include "cvv.mm"
include "ctopon.mm"
include "0ex.mm"
include "tmdtopon.mm"
include "adantl.mm"
include "fveq2i.mm"
include "eqcomi.mm"
include "pttoponconst.mm"
include "sylancr.mm"
include "cmnd.mm"
include "tmdmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "cnmptc.mm"
include "syl5eqel.mm"
include "wn.mm"
include "cres.mm"
include "cplusg.mm"
include "cbvmptv.mm"
include "simpl1l.mm"
include "simp2l.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "adantr.mm"
include "wf.mm"
include "elmapi.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "cin.mm"
include "simpl2r.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "gsumsplit.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "simp1r.mm"
include "syl2anc.mm"
include "cuni.mm"
include "toponuni.mm"
include "ctop.mm"
include "wss.mm"
include "topontop.mm"
include "3syl.mm"
include "fconst6g.mm"
include "ssun1.mm"
include "a1i.mm"
include "xpssres.mm"
include "ax-mp.mm"
include "ptrescn.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "simp3.mm"
include "cnmpt11.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "ssun2.mm"
include "resmpt.mm"
include "cmnmnd.mm"
include "vex.mm"
include "vsnid.mm"
include "elun2.mm"
include "mp1i.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "eqtrd.mm"
include "ptpjcn.mm"
include "fvconst2g.mm"
include "eleqtrd.mm"
include "cnmpt1plusg.mm"
include "3expia.mm"
include "expcom.mm"
include "a2d.mm"
include "findcard2s.mm"
include "com12.mm"
include "3impia.mm"
include "xkopt.mm"
include "sylan.mm"
include "3adant1.mm"
include "eleqtrrd.mm"

theorem tmdgsum
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cG: class G
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cU: class U
  let wph: wff ph
  assume tmdgsum.j: |- J = ( TopOpen ` G )
  assume tmdgsum.b: |- B = ( Base ` G )

  disjoint A x
  disjoint J x
  disjoint B x
  disjoint G x
  disjoint f g
  disjoint f k
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J f
  disjoint J g
  disjoint J t
  disjoint J u
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X t
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint B f
  disjoint B g
  disjoint B k
  disjoint B t
  disjoint B u
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint U f
  disjoint U g
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint g ph
  disjoint ph x
  assert |- ( ( G e. CMnd /\ G e. TopMnd /\ A e. Fin ) -> ( x e. ( B ^m A ) |-> ( G gsum x ) ) e. ( ( J ^ko ~P A ) Cn J ) )

  proof
    cG
    ccmn
    wcel
    #
    cG
    ctmd
    wcel
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    vx
    cB
    cA
    cmap
    co
    #
    cG
    vx
    cv
    #
    cgsu
    co
    #
    cmpt
    #
    cA
    cJ
    csn
    #
    cxp
    #
    cpt
    cfv
    #
    cJ
    ccn
    co
    #
    cJ
    cA
    cpw
    cxko
    co
    #
    cJ
    ccn
    co
    @0
    @1
    @2
    @7
    @11
    wcel
    #
    @2
    @0
    @1
    wa
    #
    @13
    @14
    vx
    cB
    vw
    cv
    #
    cmap
    co
    #
    @6
    cmpt
    #
    @15
    @8
    cxp
    #
    cpt
    cfv
    #
    cJ
    ccn
    co
    #
    wcel
    #
    wi
    @14
    vx
    cB
    c0
    cmap
    co
    #
    @6
    cmpt
    #
    c0
    cpt
    cfv
    #
    cJ
    ccn
    co
    #
    wcel
    #
    wi
    @14
    vx
    cB
    vy
    cv
    #
    cmap
    co
    #
    @6
    cmpt
    #
    @27
    @8
    cxp
    #
    cpt
    cfv
    #
    cJ
    ccn
    co
    #
    wcel
    #
    wi
    @14
    vx
    cB
    @27
    vz
    cv
    #
    csn
    #
    cun
    #
    cmap
    co
    #
    @6
    cmpt
    #
    @36
    @8
    cxp
    #
    cpt
    cfv
    #
    cJ
    ccn
    co
    #
    wcel
    #
    wi
    @14
    @13
    wi
    vw
    vy
    vz
    cA
    @15
    c0
    wceq
    #
    @21
    @26
    @14
    @43
    @17
    @23
    @20
    @25
    @43
    vx
    @16
    @22
    @6
    @15
    c0
    cB
    cmap
    oveq2
    mpteq1d
    @43
    @19
    @24
    cJ
    ccn
    @43
    @18
    c0
    cpt
    @43
    @18
    c0
    @8
    cxp
    #
    c0
    @15
    c0
    @8
    xpeq1
    @8
    0xp
    #
    syl6eq
    fveq2d
    oveq1d
    eleq12d
    imbi2d
    @15
    @27
    wceq
    #
    @21
    @33
    @14
    @46
    @17
    @29
    @20
    @32
    @46
    vx
    @16
    @28
    @6
    @15
    @27
    cB
    cmap
    oveq2
    mpteq1d
    @46
    @19
    @31
    cJ
    ccn
    @46
    @18
    @30
    cpt
    @15
    @27
    @8
    xpeq1
    fveq2d
    oveq1d
    eleq12d
    imbi2d
    @15
    @36
    wceq
    #
    @21
    @42
    @14
    @47
    @17
    @38
    @20
    @41
    @47
    vx
    @16
    @37
    @6
    @15
    @36
    cB
    cmap
    oveq2
    mpteq1d
    @47
    @19
    @40
    cJ
    ccn
    @47
    @18
    @39
    cpt
    @15
    @36
    @8
    xpeq1
    fveq2d
    oveq1d
    eleq12d
    imbi2d
    @15
    cA
    wceq
    #
    @21
    @13
    @14
    @48
    @17
    @7
    @20
    @11
    @48
    vx
    @16
    @4
    @6
    @15
    cA
    cB
    cmap
    oveq2
    mpteq1d
    @48
    @19
    @10
    cJ
    ccn
    @48
    @18
    @9
    cpt
    @15
    cA
    @8
    xpeq1
    fveq2d
    oveq1d
    eleq12d
    imbi2d
    @14
    @23
    vx
    @22
    cG
    c0g
    cfv
    #
    cmpt
    @25
    vx
    @22
    @6
    @49
    @5
    @22
    wcel
    #
    @6
    cG
    c0
    cgsu
    co
    @49
    @50
    @5
    c0
    cG
    cgsu
    @50
    @5
    c0
    wfn
    @5
    c0
    wceq
    @5
    cB
    c0
    elmapfn
    @5
    fn0
    sylib
    oveq2d
    cG
    @49
    @49
    eqid
    #
    gsum0
    syl6eq
    mpteq2ia
    @14
    vx
    @49
    @24
    cJ
    @22
    cB
    @14
    c0
    cvv
    wcel
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @24
    @22
    ctopon
    cfv
    wcel
    0ex
    @1
    @52
    @0
    cG
    cJ
    cB
    tmdgsum.j
    tmdgsum.b
    tmdtopon
    #
    adantl
    #
    c0
    cJ
    @24
    cvv
    cB
    @44
    cpt
    cfv
    @24
    @44
    c0
    cpt
    @45
    fveq2i
    eqcomi
    pttoponconst
    sylancr
    @54
    @14
    cG
    cmnd
    wcel
    #
    @49
    cB
    wcel
    @1
    @55
    @0
    cG
    tmdmnd
    adantl
    cB
    cG
    @49
    tmdgsum.b
    @51
    mndidcl
    syl
    cnmptc
    syl5eqel
    @27
    cfn
    wcel
    #
    @34
    @27
    wcel
    wn
    #
    wa
    #
    @14
    @33
    @42
    @14
    @58
    @33
    @42
    wi
    @14
    @58
    @33
    @42
    @14
    @58
    @33
    w3a
    #
    @38
    vw
    @37
    cG
    @15
    @27
    cres
    #
    cgsu
    co
    #
    cG
    @15
    @35
    cres
    #
    cgsu
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    @41
    @59
    @38
    vw
    @37
    cG
    @15
    cgsu
    co
    #
    cmpt
    @66
    vx
    vw
    @37
    @6
    @67
    @5
    @15
    cG
    cgsu
    oveq2
    cbvmptv
    @59
    vw
    @37
    @67
    @65
    @59
    @15
    @37
    wcel
    #
    wa
    #
    @36
    cB
    @27
    @35
    @64
    @15
    cG
    cfn
    @49
    tmdgsum.b
    @51
    @64
    eqid
    #
    @0
    @1
    @58
    @33
    @68
    simpl1l
    #
    @59
    @36
    cfn
    wcel
    #
    @68
    @59
    @56
    @35
    cfn
    wcel
    @72
    @14
    @56
    @57
    @33
    simp2l
    #
    @34
    snfi
    @27
    @35
    unfi
    sylancl
    #
    adantr
    #
    @68
    @36
    cB
    @15
    wf
    @59
    @15
    cB
    @36
    elmapi
    adantl
    #
    @69
    @36
    cB
    @15
    cvv
    @49
    @76
    @75
    @69
    cG
    c0g
    fvexd
    fdmfifsupp
    @69
    @57
    @27
    @35
    cin
    c0
    wceq
    @56
    @57
    @14
    @33
    @68
    simpl2r
    @27
    @34
    disjsn
    sylibr
    @69
    @36
    eqidd
    gsumsplit
    mpteq2dva
    syl5eq
    @59
    vw
    @61
    @63
    @64
    cG
    cJ
    @40
    @37
    tmdgsum.j
    @70
    @0
    @1
    @58
    @33
    simp1r
    #
    @59
    @72
    @52
    @40
    @37
    ctopon
    cfv
    wcel
    #
    @74
    @59
    @1
    @52
    @77
    @53
    syl
    #
    @36
    cJ
    @40
    cfn
    cB
    @40
    eqid
    #
    pttoponconst
    syl2anc
    #
    @59
    vw
    vx
    @60
    @6
    @61
    @40
    @31
    cJ
    @37
    @28
    @81
    @59
    vw
    @37
    @60
    cmpt
    vw
    @40
    cuni
    #
    @60
    cmpt
    #
    @40
    @31
    ccn
    co
    #
    @59
    vw
    @37
    @82
    @60
    @59
    @78
    @37
    @82
    wceq
    @81
    @37
    @40
    toponuni
    syl
    #
    mpteq1d
    @59
    @72
    @36
    ctop
    @39
    wf
    #
    @27
    @36
    wss
    #
    @83
    @84
    wcel
    @74
    @59
    cJ
    ctop
    wcel
    #
    @86
    @59
    @1
    @52
    @88
    @77
    @53
    cB
    cJ
    topontop
    #
    3syl
    #
    @36
    cJ
    ctop
    fconst6g
    syl
    #
    @87
    @59
    @27
    @35
    ssun1
    #
    a1i
    vw
    @36
    @27
    @39
    @40
    @31
    cfn
    @82
    @82
    eqid
    #
    @80
    @30
    @39
    @27
    cres
    #
    cpt
    @94
    @30
    @87
    @94
    @30
    wceq
    @92
    @36
    @8
    @27
    xpssres
    ax-mp
    eqcomi
    fveq2i
    ptrescn
    syl3anc
    eqeltrd
    @59
    @56
    @52
    @31
    @28
    ctopon
    cfv
    wcel
    @73
    @79
    @27
    cJ
    @31
    cfn
    cB
    @31
    eqid
    pttoponconst
    syl2anc
    @14
    @58
    @33
    simp3
    @5
    @60
    cG
    cgsu
    oveq2
    cnmpt11
    @59
    vw
    @37
    @63
    cmpt
    vw
    @37
    @34
    @15
    cfv
    #
    cmpt
    #
    @41
    @59
    vw
    @37
    @63
    @95
    @69
    @63
    cG
    vk
    @35
    vk
    cv
    #
    @15
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @95
    @69
    @62
    @99
    cG
    cgsu
    @69
    @62
    vk
    @36
    @98
    cmpt
    #
    @35
    cres
    #
    @99
    @69
    @15
    @101
    @35
    @69
    vk
    @36
    cB
    @15
    @76
    feqmptd
    reseq1d
    @35
    @36
    wss
    @102
    @99
    wceq
    @35
    @27
    ssun2
    vk
    @36
    @35
    @98
    resmpt
    ax-mp
    syl6eq
    oveq2d
    @69
    @55
    @34
    cvv
    wcel
    #
    @95
    cB
    wcel
    @100
    @95
    wceq
    @69
    @0
    @55
    @71
    cG
    cmnmnd
    syl
    @103
    @69
    vz
    vex
    a1i
    @69
    @36
    cB
    @34
    @15
    @76
    @34
    @35
    wcel
    #
    @34
    @36
    wcel
    #
    @69
    vz
    vsnid
    #
    @34
    @35
    @27
    elun2
    #
    mp1i
    ffvelrnd
    @98
    cB
    @95
    vk
    cG
    @34
    cvv
    tmdgsum.b
    @97
    @34
    @15
    fveq2
    gsumsn
    syl3anc
    eqtrd
    mpteq2dva
    @59
    @96
    @40
    @34
    @39
    cfv
    #
    ccn
    co
    #
    @41
    @59
    @96
    vw
    @82
    @95
    cmpt
    #
    @109
    @59
    vw
    @37
    @82
    @95
    @85
    mpteq1d
    @59
    @72
    @86
    @105
    @110
    @109
    wcel
    @74
    @91
    @104
    @105
    @59
    @106
    @107
    mp1i
    #
    vw
    @36
    @39
    @34
    @40
    cfn
    @82
    @93
    @80
    ptpjcn
    syl3anc
    eqeltrd
    @59
    @108
    cJ
    @40
    ccn
    @59
    @88
    @105
    @108
    cJ
    wceq
    @90
    @111
    @36
    cJ
    @34
    ctop
    fvconst2g
    syl2anc
    oveq2d
    eleqtrd
    eqeltrd
    cnmpt1plusg
    eqeltrd
    3expia
    expcom
    a2d
    findcard2s
    com12
    3impia
    @3
    @12
    @10
    cJ
    ccn
    @1
    @2
    @12
    @10
    wceq
    #
    @0
    @1
    @88
    @2
    @112
    @1
    @52
    @88
    @53
    @89
    syl
    cA
    cJ
    cfn
    xkopt
    sylan
    3adant1
    oveq1d
    eleqtrrd
end
