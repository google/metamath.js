include "cxp.mm"
include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimivva.mm"
include "fnmpt2.mm"
include "syl.mm"
include "cop.mm"
include "cmpt.mm"
include "cv.mm"
include "wa.mm"
include "opelxpi.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "wceq.mm"
include "copab.mm"
include "cvv.mm"
include "elxp7.mm"
include "anbi1i.mm"
include "anass.mm"
include "wsbc.mm"
include "sbcbidv.mm"
include "sbcan.mm"
include "wb.mm"
include "fvex.mm"
include "sbcg.mm"
include "ax-mp.mm"
include "sbcel1v.mm"
include "anbi12i.mm"
include "bitri.mm"
include "sbceq2g.mm"
include "sbcbii.mm"
include "3bitri.mm"
include "sbceq1g.mm"
include "csbvarg.mm"
include "eqeq1i.mm"
include "3bitr3g.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "xpss.mm"
include "simprr.mm"
include "adantrr.mm"
include "eqeltrd.mm"
include "sseldi.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "eqop.mm"
include "pm5.32i.mm"
include "syl6rbb.mm"
include "bitrd.mm"
include "opabbidv.mm"
include "coprab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfcsb.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "anbi12d.mm"
include "csbeq1a.mm"
include "sylan9eqr.mm"
include "eqeq2d.mm"
include "cbvoprab12.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "csbcom.mm"
include "csbco.mm"
include "csbeq2i.mm"
include "csbopeq1a.mm"
include "syl5eqr.mm"
include "sseli.mm"
include "adantr.mm"
include "cnvoprab.mm"
include "3eqtri.mm"
include "df-mpt.mm"
include "3eqtr4g.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem f1od2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cI: class I
  let cJ: class J
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vi: setvar i
  let vj: setvar j
  assume f1od2.1: |- F = ( x e. A , y e. B |-> C )
  assume f1od2.2: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C e. W )
  assume f1od2.3: |- ( ( ph /\ z e. D ) -> ( I e. X /\ J e. Y ) )
  assume f1od2.4: |- ( ph -> ( ( ( x e. A /\ y e. B ) /\ z = C ) <-> ( z e. D /\ ( x = I /\ y = J ) ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint I x
  disjoint I y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint B a
  disjoint B i
  disjoint B j
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint D a
  disjoint I a
  disjoint J a
  disjoint a ph
  assert |- ( ph -> F : ( A X. B ) -1-1-onto-> D )

  proof
    wph
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cF
    ccnv
    #
    cD
    wfn
    #
    @0
    cD
    cF
    wf1o
    wph
    cC
    cW
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    @1
    wph
    @4
    vx
    vy
    cA
    cB
    f1od2.2
    ralrimivva
    vx
    vy
    cA
    cB
    cC
    cF
    cW
    f1od2.1
    fnmpt2
    syl
    wph
    @3
    vz
    cD
    cI
    cJ
    cop
    #
    cmpt
    #
    cD
    wfn
    #
    wph
    @5
    cX
    cY
    cxp
    #
    wcel
    #
    vz
    cD
    wral
    @7
    wph
    @9
    vz
    cD
    wph
    vz
    cv
    #
    cD
    wcel
    #
    wa
    cI
    cX
    wcel
    cJ
    cY
    wcel
    wa
    @9
    f1od2.3
    cI
    cJ
    cX
    cY
    opelxpi
    syl
    #
    ralrimiva
    vz
    cD
    @5
    @6
    @8
    @6
    eqid
    fnmpt
    syl
    wph
    cD
    @2
    @6
    wph
    va
    cv
    #
    @0
    wcel
    #
    @10
    vx
    @13
    c1st
    cfv
    #
    vy
    @13
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    wceq
    #
    wa
    #
    vz
    va
    copab
    #
    @11
    @13
    @5
    wceq
    #
    wa
    #
    vz
    va
    copab
    @2
    @6
    wph
    @20
    @23
    vz
    va
    @20
    @13
    cvv
    cvv
    cxp
    #
    wcel
    #
    @15
    cA
    wcel
    #
    @16
    cB
    wcel
    #
    wa
    #
    wa
    #
    @19
    wa
    #
    wph
    @23
    @14
    @29
    @19
    @13
    cA
    cB
    elxp7
    anbi1i
    wph
    @30
    @25
    @11
    @15
    cI
    wceq
    #
    @16
    cJ
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @23
    @30
    @25
    @28
    @19
    wa
    #
    wa
    wph
    @35
    @25
    @28
    @19
    anass
    wph
    @36
    @34
    @25
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @10
    cC
    wceq
    #
    wa
    #
    vy
    @16
    wsbc
    #
    vx
    @15
    wsbc
    #
    @11
    @37
    cI
    wceq
    #
    @39
    cJ
    wceq
    #
    wa
    #
    wa
    #
    vy
    @16
    wsbc
    #
    vx
    @15
    wsbc
    #
    @36
    @34
    wph
    @44
    @50
    vx
    @15
    wph
    @43
    @49
    vy
    @16
    f1od2.4
    sbcbidv
    sbcbidv
    @45
    @38
    @27
    wa
    #
    @10
    @17
    wceq
    #
    wa
    #
    vx
    @15
    wsbc
    @52
    vx
    @15
    wsbc
    #
    @53
    vx
    @15
    wsbc
    #
    wa
    @36
    @44
    @54
    vx
    @15
    @44
    @41
    vy
    @16
    wsbc
    #
    @42
    vy
    @16
    wsbc
    #
    wa
    @54
    @41
    @42
    vy
    @16
    sbcan
    @57
    @52
    @58
    @53
    @57
    @38
    vy
    @16
    wsbc
    #
    @40
    vy
    @16
    wsbc
    #
    wa
    @52
    @38
    @40
    vy
    @16
    sbcan
    @59
    @38
    @60
    @27
    @16
    cvv
    wcel
    #
    @59
    @38
    wb
    @13
    c2nd
    fvex
    #
    @38
    vy
    @16
    cvv
    sbcg
    ax-mp
    vy
    @16
    cB
    sbcel1v
    anbi12i
    bitri
    @61
    @58
    @53
    wb
    @62
    vy
    @16
    @10
    cC
    cvv
    sbceq2g
    ax-mp
    anbi12i
    bitri
    sbcbii
    @52
    @53
    vx
    @15
    sbcan
    @55
    @28
    @56
    @19
    @55
    @38
    vx
    @15
    wsbc
    #
    @27
    vx
    @15
    wsbc
    #
    wa
    @28
    @38
    @27
    vx
    @15
    sbcan
    @63
    @26
    @64
    @27
    vx
    @15
    cA
    sbcel1v
    @15
    cvv
    wcel
    #
    @64
    @27
    wb
    @13
    c1st
    fvex
    #
    @27
    vx
    @15
    cvv
    sbcg
    ax-mp
    anbi12i
    bitri
    @65
    @56
    @19
    wb
    @66
    vx
    @15
    @10
    @17
    cvv
    sbceq2g
    ax-mp
    anbi12i
    3bitri
    @51
    @11
    @46
    @32
    wa
    #
    wa
    #
    vx
    @15
    wsbc
    @11
    vx
    @15
    wsbc
    #
    @67
    vx
    @15
    wsbc
    #
    wa
    @34
    @50
    @68
    vx
    @15
    @50
    @11
    vy
    @16
    wsbc
    #
    @48
    vy
    @16
    wsbc
    #
    wa
    @68
    @11
    @48
    vy
    @16
    sbcan
    @71
    @11
    @72
    @67
    @61
    @71
    @11
    wb
    @62
    @11
    vy
    @16
    cvv
    sbcg
    ax-mp
    @72
    @46
    vy
    @16
    wsbc
    #
    @47
    vy
    @16
    wsbc
    #
    wa
    @67
    @46
    @47
    vy
    @16
    sbcan
    @73
    @46
    @74
    @32
    @61
    @73
    @46
    wb
    @62
    @46
    vy
    @16
    cvv
    sbcg
    ax-mp
    @74
    vy
    @16
    @39
    csb
    #
    cJ
    wceq
    #
    @32
    @61
    @74
    @76
    wb
    @62
    vy
    @16
    @39
    cJ
    cvv
    sbceq1g
    ax-mp
    @75
    @16
    cJ
    @61
    @75
    @16
    wceq
    @62
    vy
    @16
    cvv
    csbvarg
    ax-mp
    eqeq1i
    bitri
    anbi12i
    bitri
    anbi12i
    bitri
    sbcbii
    @11
    @67
    vx
    @15
    sbcan
    @69
    @11
    @70
    @33
    @65
    @69
    @11
    wb
    @66
    @11
    vx
    @15
    cvv
    sbcg
    ax-mp
    @70
    @46
    vx
    @15
    wsbc
    #
    @32
    vx
    @15
    wsbc
    #
    wa
    @33
    @46
    @32
    vx
    @15
    sbcan
    @77
    @31
    @78
    @32
    @77
    vx
    @15
    @37
    csb
    #
    cI
    wceq
    #
    @31
    @65
    @77
    @80
    wb
    @66
    vx
    @15
    @37
    cI
    cvv
    sbceq1g
    ax-mp
    @79
    @15
    cI
    @65
    @79
    @15
    wceq
    @66
    vx
    @15
    cvv
    csbvarg
    ax-mp
    eqeq1i
    bitri
    @65
    @78
    @32
    wb
    @66
    @32
    vx
    @15
    cvv
    sbcg
    ax-mp
    anbi12i
    bitri
    anbi12i
    3bitri
    3bitr3g
    anbi2d
    syl5bb
    wph
    @23
    @25
    @23
    wa
    @35
    wph
    @23
    @25
    wph
    @23
    @25
    wph
    @23
    wa
    #
    @8
    @24
    @13
    cX
    cY
    xpss
    @81
    @13
    @5
    @8
    wph
    @11
    @22
    simprr
    wph
    @11
    @9
    @22
    @12
    adantrr
    eqeltrd
    sseldi
    ex
    pm4.71rd
    @25
    @23
    @34
    @25
    @22
    @33
    @11
    @13
    cI
    cJ
    cvv
    cvv
    eqop
    anbi2d
    pm5.32i
    syl6rbb
    bitrd
    syl5bb
    opabbidv
    @2
    @43
    vx
    vy
    vz
    coprab
    #
    ccnv
    vi
    cv
    #
    cA
    wcel
    #
    vj
    cv
    #
    cB
    wcel
    #
    wa
    #
    @10
    vx
    @83
    vy
    @85
    cC
    csb
    #
    csb
    #
    wceq
    #
    wa
    #
    vi
    vj
    vz
    coprab
    #
    ccnv
    @21
    cF
    @82
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @82
    f1od2.1
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    eqtri
    cnveqi
    @82
    @92
    @43
    @91
    vx
    vy
    vz
    vi
    vj
    @43
    vi
    nfv
    @43
    vj
    nfv
    @87
    @90
    vx
    @87
    vx
    nfv
    vx
    @10
    @89
    vx
    @83
    @88
    nfcsb1v
    nfeq2
    nfan
    @87
    @90
    vy
    @87
    vy
    nfv
    vy
    @10
    @89
    vy
    vx
    @83
    @88
    vy
    @83
    nfcv
    vy
    @85
    cC
    nfcsb1v
    nfcsb
    nfeq2
    nfan
    @37
    @83
    wceq
    #
    @39
    @85
    wceq
    #
    wa
    #
    @41
    @87
    @42
    @90
    @95
    @38
    @84
    @40
    @86
    @95
    @37
    @83
    cA
    @93
    @94
    simpl
    eleq1d
    @95
    @39
    @85
    cB
    @93
    @94
    simpr
    eleq1d
    anbi12d
    @95
    cC
    @89
    @10
    @94
    @93
    cC
    @88
    @89
    vy
    @85
    cC
    csbeq1a
    vx
    @83
    @88
    csbeq1a
    sylan9eqr
    eqeq2d
    anbi12d
    cbvoprab12
    cnveqi
    @91
    @20
    vi
    vj
    vz
    va
    @13
    @83
    @85
    cop
    #
    wceq
    #
    @14
    @87
    @19
    @90
    @97
    @14
    @96
    @0
    wcel
    @87
    @13
    @96
    @0
    eleq1
    @83
    @85
    cA
    cB
    opelxp
    syl6bb
    @97
    @18
    @89
    @10
    @97
    @18
    vi
    @15
    vj
    @16
    @89
    csb
    #
    csb
    #
    @89
    @99
    vi
    @15
    vx
    @83
    @17
    csb
    #
    csb
    @18
    vi
    @15
    @98
    @100
    @98
    vx
    @83
    vj
    @16
    @88
    csb
    #
    csb
    @100
    vj
    vx
    @16
    @83
    @88
    csbcom
    vx
    @83
    @101
    @17
    vy
    vj
    @16
    cC
    csbco
    csbeq2i
    eqtri
    csbeq2i
    vx
    vi
    @15
    @17
    csbco
    eqtri
    vi
    vj
    @13
    @89
    csbopeq1a
    syl5eqr
    eqeq2d
    anbi12d
    @14
    @25
    @19
    @0
    @24
    @13
    cA
    cB
    xpss
    sseli
    adantr
    cnvoprab
    3eqtri
    vz
    va
    cD
    @5
    df-mpt
    3eqtr4g
    fneq1d
    mpbird
    @0
    cD
    cF
    dff1o4
    sylanbrc
end
