include "wss.mm"
include "ciun.mm"
include "csu.mm"
include "wceq.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sseq1.mm"
include "iuneq1.mm"
include "0iun.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "sumeq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cc0.mm"
include "sum0.mm"
include "eqtr4i.mm"
include "2a1i.mm"
include "wn.mm"
include "wa.mm"
include "id.mm"
include "unssad.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "oveq1.mm"
include "cin.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "vex.mm"
include "csbeq1.mm"
include "iunxsn.mm"
include "eqtri.mm"
include "ineq2i.mm"
include "wdisj.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "simpr.mm"
include "unssbd.mm"
include "simplr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "disjiun.mm"
include "syl13anc.mm"
include "syl5eqr.mm"
include "iunxun.mm"
include "uneq2i.mm"
include "a1i.mm"
include "wral.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "sylc.mm"
include "iunfi.mm"
include "cc.mm"
include "iunss1.mm"
include "sselda.mm"
include "wrex.mm"
include "eliun.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "imp.mm"
include "syldan.mm"
include "fsumsplit.mm"
include "eqidd.mm"
include "anassrs.mm"
include "fsumcl.mm"
include "r19.21bi.mm"
include "nfsum.mm"
include "cbvsumi.mm"
include "cvv.mm"
include "snss.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sumsn.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "ex.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fsumiun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  assume fsumiun.1: |- ( ph -> A e. Fin )
  assume fsumiun.2: |- ( ( ph /\ x e. A ) -> B e. Fin )
  assume fsumiun.3: |- ( ph -> Disj_ x e. A B )
  assume fsumiun.4: |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> C e. CC )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint k ph
  disjoint ph x
  disjoint C x
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint B u
  disjoint B w
  disjoint B z
  disjoint ph u
  disjoint ph w
  disjoint ph z
  disjoint C u
  disjoint C w
  disjoint C z
  assert |- ( ph -> sum_ k e. U_ x e. A B C = sum_ x e. A sum_ k e. B C )

  proof
    wph
    cA
    cA
    wss
    #
    vx
    cA
    cB
    ciun
    #
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
    wceq
    #
    cA
    ssid
    cA
    cfn
    wcel
    #
    wph
    @0
    @5
    wi
    #
    fsumiun.1
    wph
    vu
    cv
    #
    cA
    wss
    #
    vx
    @8
    cB
    ciun
    #
    cC
    vk
    csu
    #
    @8
    @3
    vx
    csu
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    cA
    wss
    #
    c0
    cC
    vk
    csu
    #
    c0
    @3
    vx
    csu
    #
    wceq
    #
    wi
    #
    wi
    wph
    vz
    cv
    #
    cA
    wss
    #
    vx
    @20
    cB
    ciun
    #
    cC
    vk
    csu
    #
    @20
    @3
    vx
    csu
    #
    wceq
    #
    wi
    #
    wi
    #
    wph
    @20
    vw
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    vx
    @30
    cB
    ciun
    #
    cC
    vk
    csu
    #
    @30
    @3
    vx
    csu
    #
    wceq
    #
    wi
    #
    wi
    #
    wph
    @7
    wi
    vu
    vz
    vw
    cA
    @8
    c0
    wceq
    #
    @14
    @19
    wph
    @38
    @9
    @15
    @13
    @18
    @8
    c0
    cA
    sseq1
    @38
    @11
    @16
    @12
    @17
    @38
    @10
    c0
    cC
    vk
    @38
    @10
    vx
    c0
    cB
    ciun
    c0
    vx
    @8
    c0
    cB
    iuneq1
    vx
    cB
    0iun
    syl6eq
    sumeq1d
    @8
    c0
    @3
    vx
    sumeq1
    eqeq12d
    imbi12d
    imbi2d
    vu
    vz
    weq
    #
    @14
    @26
    wph
    @39
    @9
    @21
    @13
    @25
    @8
    @20
    cA
    sseq1
    @39
    @11
    @23
    @12
    @24
    @39
    @10
    @22
    cC
    vk
    vx
    @8
    @20
    cB
    iuneq1
    sumeq1d
    @8
    @20
    @3
    vx
    sumeq1
    eqeq12d
    imbi12d
    imbi2d
    @8
    @30
    wceq
    #
    @14
    @36
    wph
    @40
    @9
    @31
    @13
    @35
    @8
    @30
    cA
    sseq1
    @40
    @11
    @33
    @12
    @34
    @40
    @10
    @32
    cC
    vk
    vx
    @8
    @30
    cB
    iuneq1
    sumeq1d
    @8
    @30
    @3
    vx
    sumeq1
    eqeq12d
    imbi12d
    imbi2d
    @8
    cA
    wceq
    #
    @14
    @7
    wph
    @41
    @9
    @0
    @13
    @5
    @8
    cA
    cA
    sseq1
    @41
    @11
    @2
    @12
    @4
    @41
    @10
    @1
    cC
    vk
    vx
    @8
    cA
    cB
    iuneq1
    sumeq1d
    @8
    cA
    @3
    vx
    sumeq1
    eqeq12d
    imbi12d
    imbi2d
    @18
    wph
    @15
    @16
    cc0
    @17
    cC
    vk
    sum0
    @3
    vx
    sum0
    eqtr4i
    2a1i
    @28
    @20
    wcel
    wn
    #
    @27
    @37
    wi
    @20
    cfn
    wcel
    @42
    wph
    @26
    @36
    wph
    @42
    @26
    @36
    wi
    @26
    @31
    @25
    wi
    wph
    @42
    wa
    #
    @36
    @31
    @21
    @25
    @31
    @20
    @29
    cA
    @31
    id
    unssad
    #
    imim1i
    @43
    @31
    @25
    @35
    @43
    @31
    @25
    @35
    wi
    @25
    @35
    @43
    @31
    wa
    #
    @23
    vx
    @28
    cB
    csb
    #
    cC
    vk
    csu
    #
    caddc
    co
    #
    @24
    @47
    caddc
    co
    #
    wceq
    @23
    @24
    @47
    caddc
    oveq1
    @45
    @33
    @48
    @34
    @49
    @45
    @22
    @46
    cC
    @32
    vk
    @45
    @22
    @46
    cin
    @22
    vx
    @29
    cB
    ciun
    #
    cin
    #
    c0
    @50
    @46
    @22
    @50
    vz
    @29
    vx
    @20
    cB
    csb
    #
    ciun
    @46
    vx
    vz
    @29
    cB
    @52
    vz
    cB
    nfcv
    vx
    @20
    cB
    nfcsb1v
    #
    vx
    @20
    cB
    csbeq1a
    #
    cbviun
    vz
    @28
    @52
    @46
    vw
    vex
    #
    vx
    @20
    @28
    cB
    csbeq1
    #
    iunxsn
    eqtri
    #
    ineq2i
    @45
    vx
    cA
    cB
    wdisj
    #
    @21
    @29
    cA
    wss
    #
    @20
    @29
    cin
    c0
    wceq
    #
    @51
    c0
    wceq
    wph
    @58
    @42
    @31
    fsumiun.3
    ad2antrr
    @31
    @21
    @43
    @44
    adantl
    @45
    @20
    @29
    cA
    @43
    @31
    simpr
    #
    unssbd
    #
    @45
    @42
    @60
    wph
    @42
    @31
    simplr
    @20
    @28
    disjsn
    sylibr
    #
    vx
    cA
    cB
    @20
    @29
    disjiun
    syl13anc
    syl5eqr
    @32
    @22
    @46
    cun
    #
    wceq
    @45
    @32
    @22
    @50
    cun
    @64
    vx
    @20
    @29
    cB
    iunxun
    @50
    @46
    @22
    @57
    uneq2i
    eqtri
    a1i
    @45
    @30
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    vx
    @30
    wral
    #
    @32
    cfn
    wcel
    @45
    @6
    @31
    @65
    wph
    @6
    @42
    @31
    fsumiun.1
    ad2antrr
    @61
    cA
    @30
    ssfi
    syl2anc
    #
    @45
    @31
    @66
    vx
    cA
    wral
    #
    @67
    @61
    wph
    @69
    @42
    @31
    wph
    @66
    vx
    cA
    fsumiun.2
    ralrimiva
    ad2antrr
    @66
    vx
    @30
    cA
    ssralv
    sylc
    vx
    @30
    cB
    iunfi
    syl2anc
    @45
    vk
    cv
    #
    @32
    wcel
    @70
    @1
    wcel
    #
    cC
    cc
    wcel
    #
    @45
    @32
    @1
    @70
    @31
    @32
    @1
    wss
    @43
    vx
    @30
    cA
    cB
    iunss1
    adantl
    sselda
    @45
    @71
    @72
    @71
    @70
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @45
    @72
    vx
    @70
    cA
    cB
    eliun
    wph
    @74
    @72
    wi
    @42
    @31
    wph
    @73
    @72
    vx
    cA
    fsumiun.4
    rexlimdvaa
    ad2antrr
    syl5bi
    imp
    syldan
    fsumsplit
    @45
    @34
    @24
    @29
    @3
    vx
    csu
    #
    caddc
    co
    @49
    @45
    @20
    @29
    @3
    @30
    vx
    @63
    @45
    @30
    eqidd
    @68
    @45
    vx
    cv
    #
    @30
    wcel
    @76
    cA
    wcel
    #
    @3
    cc
    wcel
    #
    @45
    @30
    cA
    @76
    @61
    sselda
    @45
    @78
    vx
    cA
    wph
    @78
    vx
    cA
    wral
    #
    @42
    @31
    wph
    @78
    vx
    cA
    wph
    @77
    wa
    cB
    cC
    vk
    fsumiun.2
    wph
    @77
    @73
    @72
    fsumiun.4
    anassrs
    fsumcl
    ralrimiva
    ad2antrr
    #
    r19.21bi
    syldan
    fsumsplit
    @45
    @75
    @47
    @24
    caddc
    @45
    @75
    @29
    @52
    cC
    vk
    csu
    #
    vz
    csu
    #
    @47
    @29
    @3
    @81
    vx
    vz
    vz
    @3
    nfcv
    vx
    @52
    cC
    vk
    @53
    vx
    cC
    nfcv
    #
    nfsum
    vx
    vz
    weq
    cB
    @52
    cC
    vk
    @54
    sumeq1d
    cbvsumi
    @45
    @28
    cvv
    wcel
    @47
    cc
    wcel
    #
    @82
    @47
    wceq
    @55
    @45
    @28
    cA
    wcel
    #
    @79
    @84
    @45
    @59
    @85
    @62
    @28
    cA
    @55
    snss
    sylibr
    @80
    @78
    @84
    vx
    @28
    cA
    vx
    @47
    cc
    vx
    @46
    cC
    vk
    vx
    @28
    cB
    nfcsb1v
    @83
    nfsum
    nfel1
    vx
    vw
    weq
    #
    @3
    @47
    cc
    @86
    cB
    @46
    cC
    vk
    vx
    @28
    cB
    csbeq1a
    sumeq1d
    eleq1d
    rspc
    sylc
    @81
    @47
    vz
    @28
    cvv
    vz
    vw
    weq
    @52
    @46
    cC
    vk
    @56
    sumeq1d
    sumsn
    sylancr
    syl5eq
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    ex
    a2d
    syl5
    expcom
    a2d
    adantl
    findcard2s
    mpcom
    mpi
end
