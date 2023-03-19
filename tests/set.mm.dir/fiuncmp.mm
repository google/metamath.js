include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "wral.mm"
include "w3a.mm"
include "wss.mm"
include "ciun.mm"
include "ssid.mm"
include "wi.mm"
include "simp2.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "iuneq1.mm"
include "0iun.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "rest0.mm"
include "0cmp.mm"
include "syl6eqel.mm"
include "3ad2ant1.mm"
include "a1d.mm"
include "ssun1.mm"
include "id.mm"
include "syl5ss.mm"
include "imim1i.mm"
include "wa.mm"
include "cuni.mm"
include "cin.mm"
include "csb.mm"
include "cvv.mm"
include "simpl1.mm"
include "iunxun.mm"
include "simprr.mm"
include "cmptop.mm"
include "restrcl.mm"
include "simprd.mm"
include "3syl.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "vex.mm"
include "csbeq1.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "ssun2.mm"
include "simprl.mm"
include "snss.mm"
include "sylibr.mm"
include "simpl3.mm"
include "nfv.mm"
include "nfov.mm"
include "nfel1.mm"
include "cbvral.mm"
include "sylib.mm"
include "rspcv.mm"
include "sylc.mm"
include "syl5eqel.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resttop.mm"
include "eqid.mm"
include "restin.mm"
include "unieqd.mm"
include "inss2.mm"
include "sseqtr4i.mm"
include "restuni.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "uneq2i.mm"
include "ineq1i.mm"
include "indir.mm"
include "inss1.mm"
include "sstri.mm"
include "a1i.mm"
include "restabs.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "eqsstr3i.mm"
include "uncmp.mm"
include "syl22anc.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "a2i.mm"
include "findcard2.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fiuncmp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  assume fiuncmp.1: |- X = U. J

  disjoint A x
  disjoint J x
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B y
  disjoint B z
  disjoint J t
  disjoint J y
  disjoint J z
  assert |- ( ( J e. Top /\ A e. Fin /\ A. x e. A ( J |`t B ) e. Comp ) -> ( J |`t U_ x e. A B ) e. Comp )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cfn
    wcel
    #
    cJ
    cB
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    cA
    wral
    #
    w3a
    #
    cA
    cA
    wss
    #
    cJ
    vx
    cA
    cB
    ciun
    #
    crest
    co
    #
    ccmp
    wcel
    #
    cA
    ssid
    @1
    @5
    @6
    @9
    wi
    #
    @0
    @1
    @4
    simp2
    @5
    vt
    cv
    #
    cA
    wss
    #
    cJ
    vx
    @11
    cB
    ciun
    #
    crest
    co
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    @5
    c0
    cA
    wss
    #
    cJ
    c0
    crest
    co
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    @5
    vy
    cv
    #
    cA
    wss
    #
    cJ
    vx
    @21
    cB
    ciun
    #
    crest
    co
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    #
    @5
    @21
    vz
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    cJ
    vx
    @30
    cB
    ciun
    #
    crest
    co
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    #
    @5
    @10
    wi
    vt
    vy
    vz
    cA
    @11
    c0
    wceq
    #
    @16
    @20
    @5
    @37
    @12
    @17
    @15
    @19
    @11
    c0
    cA
    sseq1
    @37
    @14
    @18
    ccmp
    @37
    @13
    c0
    cJ
    crest
    @37
    @13
    vx
    c0
    cB
    ciun
    c0
    vx
    @11
    c0
    cB
    iuneq1
    vx
    cB
    0iun
    syl6eq
    oveq2d
    eleq1d
    imbi12d
    imbi2d
    @11
    @21
    wceq
    #
    @16
    @26
    @5
    @38
    @12
    @22
    @15
    @25
    @11
    @21
    cA
    sseq1
    @38
    @14
    @24
    ccmp
    @38
    @13
    @23
    cJ
    crest
    vx
    @11
    @21
    cB
    iuneq1
    oveq2d
    eleq1d
    imbi12d
    imbi2d
    @11
    @30
    wceq
    #
    @16
    @35
    @5
    @39
    @12
    @31
    @15
    @34
    @11
    @30
    cA
    sseq1
    @39
    @14
    @33
    ccmp
    @39
    @13
    @32
    cJ
    crest
    vx
    @11
    @30
    cB
    iuneq1
    oveq2d
    eleq1d
    imbi12d
    imbi2d
    @11
    cA
    wceq
    #
    @16
    @10
    @5
    @40
    @12
    @6
    @15
    @9
    @11
    cA
    cA
    sseq1
    @40
    @14
    @8
    ccmp
    @40
    @13
    @7
    cJ
    crest
    vx
    @11
    cA
    cB
    iuneq1
    oveq2d
    eleq1d
    imbi12d
    imbi2d
    @5
    @19
    @17
    @0
    @1
    @19
    @4
    @0
    @18
    c0
    csn
    ccmp
    cJ
    rest0
    0cmp
    syl6eqel
    3ad2ant1
    a1d
    @27
    @36
    wi
    @21
    cfn
    wcel
    @5
    @26
    @35
    @26
    @31
    @25
    wi
    @5
    @35
    @31
    @22
    @25
    @31
    @21
    @30
    cA
    @21
    @29
    ssun1
    @31
    id
    syl5ss
    imim1i
    @5
    @31
    @25
    @34
    @5
    @31
    @25
    @34
    @5
    @31
    @25
    wa
    #
    wa
    #
    @33
    ctop
    wcel
    #
    @33
    cuni
    #
    @23
    cJ
    cuni
    #
    cin
    #
    vx
    @28
    cB
    csb
    #
    @45
    cin
    #
    cun
    #
    wceq
    @33
    @46
    crest
    co
    #
    ccmp
    wcel
    @33
    @48
    crest
    co
    #
    ccmp
    wcel
    @34
    @42
    @0
    @32
    cvv
    wcel
    #
    @43
    @0
    @1
    @4
    @41
    simpl1
    #
    @42
    @32
    @23
    vx
    @29
    cB
    ciun
    #
    cun
    #
    cvv
    vx
    @21
    @29
    cB
    iunxun
    #
    @42
    @23
    cvv
    wcel
    #
    @54
    cvv
    wcel
    @55
    cvv
    wcel
    @42
    @25
    @24
    ctop
    wcel
    #
    @57
    @5
    @31
    @25
    simprr
    #
    @24
    cmptop
    @58
    cJ
    cvv
    wcel
    #
    @57
    @23
    cJ
    restrcl
    simprd
    3syl
    #
    @42
    @54
    @47
    cvv
    @54
    vt
    @29
    vx
    @11
    cB
    csb
    #
    ciun
    @47
    vx
    vt
    @29
    cB
    @62
    vt
    cB
    nfcv
    vx
    @11
    cB
    nfcsb1v
    #
    vx
    @11
    cB
    csbeq1a
    #
    cbviun
    vt
    @28
    @62
    @47
    vz
    vex
    #
    vx
    @11
    @28
    cB
    csbeq1
    #
    iunxsn
    eqtri
    #
    @42
    cJ
    @47
    crest
    co
    #
    ccmp
    wcel
    #
    @68
    ctop
    wcel
    #
    @47
    cvv
    wcel
    #
    @42
    @28
    cA
    wcel
    #
    cJ
    @62
    crest
    co
    #
    ccmp
    wcel
    #
    vt
    cA
    wral
    #
    @69
    @42
    @29
    cA
    wss
    @72
    @42
    @29
    @30
    cA
    @29
    @21
    ssun2
    @5
    @31
    @25
    simprl
    syl5ss
    @28
    cA
    @65
    snss
    sylibr
    @42
    @4
    @75
    @0
    @1
    @4
    @41
    simpl3
    @3
    @74
    vx
    vt
    cA
    @3
    vt
    nfv
    vx
    @73
    ccmp
    vx
    cJ
    @62
    crest
    vx
    cJ
    nfcv
    vx
    crest
    nfcv
    @63
    nfov
    nfel1
    vx
    cv
    @11
    wceq
    #
    @2
    @73
    ccmp
    @76
    cB
    @62
    cJ
    crest
    @64
    oveq2d
    eleq1d
    cbvral
    sylib
    @74
    @69
    vt
    @28
    cA
    @11
    @28
    wceq
    #
    @73
    @68
    ccmp
    @77
    @62
    @47
    cJ
    crest
    @66
    oveq2d
    eleq1d
    rspcv
    sylc
    #
    @68
    cmptop
    @70
    @60
    @71
    @47
    cJ
    restrcl
    simprd
    3syl
    #
    syl5eqel
    @23
    @54
    cvv
    cvv
    unexg
    syl2anc
    syl5eqel
    #
    @32
    cJ
    cvv
    resttop
    syl2anc
    @42
    @44
    @32
    @45
    cin
    #
    @49
    @42
    @44
    cJ
    @81
    crest
    co
    #
    cuni
    #
    @81
    @42
    @33
    @82
    @42
    @0
    @52
    @33
    @82
    wceq
    @53
    @80
    @32
    cJ
    ctop
    cvv
    @45
    @45
    eqid
    #
    restin
    syl2anc
    unieqd
    @42
    @0
    @81
    cX
    wss
    @81
    @83
    wceq
    @53
    @81
    @45
    cX
    @32
    @45
    inss2
    fiuncmp.1
    sseqtr4i
    @81
    cJ
    cX
    fiuncmp.1
    restuni
    sylancl
    eqtr4d
    @81
    @23
    @47
    cun
    #
    @45
    cin
    @49
    @32
    @85
    @45
    @32
    @55
    @85
    @56
    @54
    @47
    @23
    @67
    uneq2i
    eqtri
    ineq1i
    @23
    @47
    @45
    indir
    eqtri
    syl6eq
    @42
    @50
    @24
    ccmp
    @42
    @50
    cJ
    @46
    crest
    co
    #
    @24
    @42
    @0
    @46
    @32
    wss
    #
    @52
    @50
    @86
    wceq
    @53
    @87
    @42
    @46
    @23
    @32
    @23
    @45
    inss1
    @23
    @55
    @32
    @23
    @54
    ssun1
    @56
    sseqtr4i
    sstri
    a1i
    @80
    @46
    @32
    cJ
    ctop
    cvv
    restabs
    syl3anc
    @42
    @0
    @57
    @24
    @86
    wceq
    @53
    @61
    @23
    cJ
    ctop
    cvv
    @45
    @84
    restin
    syl2anc
    eqtr4d
    @59
    eqeltrd
    @42
    @51
    @68
    ccmp
    @42
    @51
    cJ
    @48
    crest
    co
    #
    @68
    @42
    @0
    @48
    @32
    wss
    #
    @52
    @51
    @88
    wceq
    @53
    @89
    @42
    @48
    @47
    @32
    @47
    @45
    inss1
    @47
    @54
    @32
    @67
    @54
    @55
    @32
    @54
    @23
    ssun2
    @56
    sseqtr4i
    eqsstr3i
    sstri
    a1i
    @80
    @48
    @32
    cJ
    ctop
    cvv
    restabs
    syl3anc
    @42
    @0
    @71
    @68
    @88
    wceq
    @53
    @79
    @47
    cJ
    ctop
    cvv
    @45
    @84
    restin
    syl2anc
    eqtr4d
    @78
    eqeltrd
    @46
    @48
    @33
    @44
    @44
    eqid
    uncmp
    syl22anc
    exp32
    a2d
    syl5
    a2i
    a1i
    findcard2
    mpcom
    mpi
end
