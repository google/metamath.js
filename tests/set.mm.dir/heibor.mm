include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "ccmp.mm"
include "wa.mm"
include "cms.mm"
include "ctotbnd.mm"
include "heibor1.mm"
include "cmetmet.mm"
include "adantr.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cxmt.mm"
include "metxmet.mm"
include "mopntop.mm"
include "3syl.mm"
include "cn0.mm"
include "wf.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cbl.mm"
include "ciun.mm"
include "wex.mm"
include "crp.mm"
include "istotbnd.mm"
include "simprbi.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "expcom.mm"
include "adantl.mm"
include "oveq1.mm"
include "ac6sfi.mm"
include "adantrl.mm"
include "w3a.mm"
include "crn.mm"
include "wss.mm"
include "simp3l.mm"
include "frn.mm"
include "syl.mm"
include "mopnuni.mm"
include "3ad2ant1.mm"
include "sseqtrd.mm"
include "cmopn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "uniex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "simp2l.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "elind.mm"
include "eleq2d.mm"
include "rexrn.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "simp3r.mm"
include "uniiun.mm"
include "iuneq2.mm"
include "syl5eq.mm"
include "simp2r.mm"
include "3eqtr2rd.mm"
include "iuneq1.mm"
include "rspcev.mm"
include "3expia.mm"
include "adantrrr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "ralrimdva.mm"
include "pwex.mm"
include "inex1.mm"
include "com.mm"
include "nn0ennn.mm"
include "nnenom.mm"
include "entri.mm"
include "axcc4.mm"
include "syl6.mm"
include "elpwi.mm"
include "cmpt2.mm"
include "wn.mm"
include "cab.mm"
include "copab.mm"
include "eqid.mm"
include "simpl.mm"
include "pweqd.mm"
include "ineq1d.mm"
include "feq3d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "cbviunv.mm"
include "id.mm"
include "inss1.mm"
include "syl5sseqr.mm"
include "fss.mm"
include "syl2anr.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "sselda.mm"
include "simplr.mm"
include "weq.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "iuneq2dv.mm"
include "biimprd.mm"
include "ralimdva.mm"
include "impr.mm"
include "fveq2.mm"
include "iuneq1d.mm"
include "eqtrd.mm"
include "cbvralv.mm"
include "heiborlem10.mm"
include "exp32.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "ex.mm"
include "imp.mm"
include "iscmp.mm"
include "sylanbrc.mm"
include "jca.mm"
include "impbii.mm"

theorem heibor
  let cD: class D
  let cJ: class J
  let cX: class X
  let vn: setvar n
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let vr: setvar r
  let vu: setvar u
  let cF: class F
  let vg: setvar g
  let cG: class G
  let wph: wff ph
  let vm: setvar m
  let vv: setvar v
  let vz: setvar z
  let cM: class M
  let cT: class T
  let cB: class B
  let cU: class U
  let wps: wff ps
  let cS: class S
  let cC: class C
  let cK: class K
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( Met ` X ) /\ J e. Comp ) <-> ( D e. ( CMet ` X ) /\ D e. ( TotBnd ` X ) ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cJ
    ccmp
    wcel
    #
    wa
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    ctotbnd
    cfv
    wcel
    #
    wa
    #
    cD
    cJ
    cX
    heibor.1
    heibor1
    @4
    @0
    @1
    @2
    @0
    @3
    cD
    cX
    cmetmet
    #
    adantr
    @4
    cJ
    ctop
    wcel
    #
    cJ
    cuni
    #
    vr
    cv
    #
    cuni
    wceq
    #
    @7
    vv
    cv
    #
    cuni
    #
    wceq
    vv
    @8
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vr
    cJ
    cpw
    #
    wral
    #
    @1
    @2
    @6
    @3
    @2
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @6
    @5
    cD
    cX
    metxmet
    #
    cD
    cJ
    cX
    heibor.1
    mopntop
    3syl
    adantr
    @2
    @3
    @16
    @2
    @3
    cn0
    @7
    cpw
    #
    cfn
    cin
    #
    vm
    cv
    #
    wf
    #
    cX
    vy
    vn
    cv
    #
    @21
    cfv
    #
    vy
    cv
    #
    c1
    c2
    @23
    cexp
    co
    #
    cdiv
    co
    #
    cD
    cbl
    cfv
    #
    co
    #
    ciun
    #
    wceq
    #
    vn
    cn0
    wral
    #
    wa
    #
    vm
    wex
    #
    @16
    @2
    @3
    cX
    vy
    vt
    cv
    #
    @29
    ciun
    #
    wceq
    #
    vt
    @20
    wrex
    #
    vn
    cn0
    wral
    @34
    @2
    @3
    @38
    vn
    cn0
    @2
    @23
    cn0
    wcel
    #
    wa
    #
    @3
    vu
    cv
    #
    cuni
    #
    cX
    wceq
    #
    @10
    @29
    wceq
    #
    vy
    cX
    wrex
    #
    vv
    @41
    wral
    #
    wa
    #
    vu
    cfn
    wrex
    #
    @38
    @39
    @3
    @48
    wi
    @2
    @3
    @39
    @48
    @3
    @43
    @10
    @25
    @8
    @28
    co
    #
    wceq
    #
    vy
    cX
    wrex
    #
    vv
    @41
    wral
    #
    wa
    #
    vu
    cfn
    wrex
    #
    vr
    crp
    wral
    #
    @27
    crp
    wcel
    @48
    @39
    @3
    @0
    @55
    vy
    vu
    cD
    cX
    vv
    vr
    istotbnd
    simprbi
    @39
    @26
    @39
    @26
    c2
    cn
    wcel
    @39
    @26
    cn
    wcel
    2nn
    c2
    @23
    nnexpcl
    mpan
    nnrpd
    rpreccld
    @54
    @48
    vr
    @27
    crp
    @8
    @27
    wceq
    #
    @53
    @47
    vu
    cfn
    @56
    @52
    @46
    @43
    @56
    @51
    @45
    vv
    @41
    @56
    @50
    @44
    vy
    cX
    @56
    @49
    @29
    @10
    @8
    @27
    @25
    @28
    oveq2
    eqeq2d
    rexbidv
    ralbidv
    anbi2d
    rexbidv
    rspccva
    syl2an
    expcom
    adantl
    @40
    @47
    @38
    vu
    cfn
    @40
    @41
    cfn
    wcel
    #
    @47
    wa
    #
    wa
    #
    @41
    cX
    @21
    wf
    #
    @10
    @10
    @21
    cfv
    #
    @27
    @28
    co
    #
    wceq
    #
    vv
    @41
    wral
    #
    wa
    #
    vm
    wex
    #
    @38
    @58
    @66
    @40
    @57
    @46
    @66
    @43
    @44
    @63
    vv
    vy
    @41
    cX
    vm
    @25
    @61
    wceq
    #
    @29
    @62
    @10
    @25
    @61
    @27
    @28
    oveq1
    #
    eqeq2d
    ac6sfi
    adantrl
    adantl
    @59
    @65
    @38
    vm
    @40
    @57
    @43
    @65
    @38
    wi
    @46
    @40
    @57
    @43
    wa
    #
    @65
    @38
    @40
    @69
    @65
    w3a
    #
    @21
    crn
    #
    @20
    wcel
    cX
    vy
    @71
    @29
    ciun
    #
    wceq
    #
    @38
    @70
    @19
    cfn
    @71
    @70
    @71
    @7
    wss
    @71
    @19
    wcel
    @70
    @71
    cX
    @7
    @70
    @60
    @71
    cX
    wss
    @40
    @69
    @60
    @64
    simp3l
    #
    @41
    cX
    @21
    frn
    syl
    @40
    @69
    cX
    @7
    wceq
    #
    @65
    @2
    @75
    @39
    @2
    @0
    @17
    @75
    @5
    @18
    cD
    cJ
    cX
    heibor.1
    mopnuni
    3syl
    #
    adantr
    3ad2ant1
    sseqtrd
    @71
    @7
    cJ
    cJ
    cD
    cmopn
    cfv
    cvv
    heibor.1
    cD
    cmopn
    fvex
    eqeltri
    uniex
    #
    elpw2
    sylibr
    @70
    @57
    @60
    @71
    cfn
    wcel
    #
    @40
    @57
    @43
    @65
    simp2l
    @74
    @60
    @57
    @41
    @71
    @21
    wfo
    #
    @78
    @60
    @21
    @41
    wfn
    #
    @79
    @41
    cX
    @21
    ffn
    #
    @41
    @21
    dffn4
    sylib
    @41
    @71
    @21
    fofi
    sylan2
    syl2anc
    elind
    @70
    @72
    vv
    @41
    @62
    ciun
    #
    @42
    cX
    @70
    @60
    @80
    @72
    @82
    wceq
    @74
    @81
    @80
    vr
    @72
    @82
    @80
    @8
    @29
    wcel
    #
    vy
    @71
    wrex
    @8
    @62
    wcel
    #
    vv
    @41
    wrex
    @8
    @72
    wcel
    @8
    @82
    wcel
    @83
    @84
    vy
    vv
    @41
    @21
    @67
    @29
    @62
    @8
    @68
    eleq2d
    rexrn
    vy
    @8
    @71
    @29
    eliun
    vv
    @8
    @41
    @62
    eliun
    3bitr4g
    eqrdv
    3syl
    @70
    @64
    @42
    @82
    wceq
    @40
    @69
    @60
    @64
    simp3r
    @64
    @42
    vv
    @41
    @10
    ciun
    @82
    vv
    @41
    uniiun
    vv
    @41
    @10
    @62
    iuneq2
    syl5eq
    syl
    @40
    @57
    @43
    @65
    simp2r
    3eqtr2rd
    @37
    @73
    vt
    @71
    @20
    @35
    @71
    wceq
    @36
    @72
    cX
    vy
    @35
    @71
    @29
    iuneq1
    eqeq2d
    rspcev
    syl2anc
    3expia
    adantrrr
    exlimdv
    mpd
    rexlimdvaa
    syld
    ralrimdva
    @37
    @31
    vt
    @20
    vm
    vn
    cn0
    @19
    cfn
    @7
    @77
    pwex
    inex1
    cn0
    cn
    com
    nn0ennn
    nnenom
    entri
    @35
    @24
    wceq
    @36
    @30
    cX
    vy
    @35
    @24
    @29
    iuneq1
    eqeq2d
    axcc4
    syl6
    @2
    @33
    @16
    vm
    @2
    @33
    @16
    @2
    @33
    wa
    #
    @14
    vr
    @15
    @8
    @15
    wcel
    @8
    cJ
    wss
    #
    @85
    @14
    @8
    cJ
    elpwi
    @85
    @86
    @9
    @13
    @85
    vt
    vz
    vv
    vu
    vz
    vm
    cX
    cn0
    vz
    cv
    #
    c1
    c2
    @21
    cexp
    co
    #
    cdiv
    co
    #
    @28
    co
    #
    cmpt2
    #
    cD
    @8
    vm
    vk
    @21
    vk
    cv
    #
    cn0
    wcel
    @35
    @92
    @21
    cfv
    #
    wcel
    #
    @35
    @92
    @91
    co
    #
    @41
    @11
    wss
    vv
    @12
    wrex
    wn
    vu
    cab
    #
    wcel
    w3a
    vt
    vk
    copab
    #
    cJ
    @96
    cX
    heibor.1
    @96
    eqid
    @97
    eqid
    @91
    eqid
    #
    @2
    @33
    simpl
    @2
    @22
    cn0
    cX
    cpw
    #
    cfn
    cin
    #
    @21
    wf
    #
    @32
    @2
    @101
    @22
    @2
    @100
    @20
    @21
    cn0
    @2
    @99
    @19
    cfn
    @2
    cX
    @7
    @76
    pweqd
    #
    ineq1d
    feq3d
    biimpar
    adantrr
    @85
    cX
    vt
    @24
    @35
    @23
    @91
    co
    #
    ciun
    #
    wceq
    #
    vn
    cn0
    wral
    #
    cX
    vt
    @93
    @95
    ciun
    #
    wceq
    #
    vk
    cn0
    wral
    @2
    @22
    @32
    @106
    @2
    @22
    wa
    #
    @31
    @105
    vn
    cn0
    @109
    @39
    wa
    #
    @105
    @31
    @110
    @104
    @30
    cX
    @110
    @104
    vy
    @24
    @25
    @23
    @91
    co
    #
    ciun
    @30
    vt
    vy
    @24
    @103
    @111
    @35
    @25
    @23
    @91
    oveq1
    cbviunv
    @110
    vy
    @24
    @111
    @29
    @110
    @25
    @24
    wcel
    #
    wa
    @25
    cX
    wcel
    @39
    @111
    @29
    wceq
    @110
    @24
    cX
    @25
    @110
    @24
    cX
    @109
    cn0
    @99
    @23
    @21
    @22
    @22
    @20
    @99
    wss
    cn0
    @99
    @21
    wf
    @2
    @22
    id
    @2
    @19
    @20
    @99
    @19
    cfn
    inss1
    @102
    syl5sseqr
    cn0
    @20
    @99
    @21
    fss
    syl2anr
    ffvelrnda
    elpwid
    sselda
    @109
    @39
    @112
    simplr
    vz
    vm
    @25
    @23
    cX
    cn0
    @90
    @29
    @91
    @25
    @89
    @28
    co
    @87
    @25
    @89
    @28
    oveq1
    vm
    vn
    weq
    #
    @89
    @27
    @25
    @28
    @113
    @88
    @26
    c1
    cdiv
    @21
    @23
    c2
    cexp
    oveq2
    oveq2d
    oveq2d
    @98
    @25
    @27
    @28
    ovex
    ovmpt2
    syl2anc
    iuneq2dv
    syl5eq
    eqeq2d
    biimprd
    ralimdva
    impr
    @105
    @108
    vn
    vk
    cn0
    vn
    vk
    weq
    #
    @104
    @107
    cX
    @114
    @104
    vt
    @93
    @103
    ciun
    @107
    @114
    vt
    @24
    @93
    @103
    @23
    @92
    @21
    fveq2
    iuneq1d
    @114
    vt
    @93
    @103
    @95
    @114
    @94
    wa
    @23
    @92
    @35
    @91
    @114
    @94
    simpl
    oveq2d
    iuneq2dv
    eqtrd
    eqeq2d
    cbvralv
    sylib
    heiborlem10
    exp32
    syl5
    ralrimiv
    ex
    exlimdv
    syld
    imp
    vr
    vv
    cJ
    @7
    @7
    eqid
    iscmp
    sylanbrc
    jca
    impbii
end
