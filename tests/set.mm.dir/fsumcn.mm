include "wss.mm"
include "csu.mm"
include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ssid.mm"
include "cfn.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cc0.mm"
include "sum0.mm"
include "mpteq2i.mm"
include "cc.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "0cnd.mm"
include "cnmptc.mm"
include "syl5eqel.mm"
include "a1d.mm"
include "wn.mm"
include "wa.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "cin.mm"
include "simplr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "simplll.mm"
include "sselda.mm"
include "simplrr.mm"
include "wral.mm"
include "wf.mm"
include "adantr.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "rsp.mm"
include "syl.mm"
include "imp.mm"
include "syl21anc.mm"
include "fsumsplit.mm"
include "simpr.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "adantrr.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "ad2ant2rl.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "rspc.mm"
include "sylc.mm"
include "sumsns.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "anassrs.mm"
include "mpteq2dva.mm"
include "nfcv.mm"
include "nfsum.mm"
include "nfcsb.mm"
include "nfov.mm"
include "sumeq2sdv.mm"
include "csbeq2dv.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "simprr.mm"
include "syl5eqelr.mm"
include "ralrimiva.mm"
include "nfmpt.mm"
include "ctx.mm"
include "addcn.mm"
include "cnmpt12f.mm"
include "eqeltrd.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fsumcn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cL: class L
  let cY: class Y
  assume fsumcn.3: |- K = ( TopOpen ` CCfld )
  assume fsumcn.4: |- ( ph -> J e. ( TopOn ` X ) )
  assume fsumcn.5: |- ( ph -> A e. Fin )
  assume fsumcn.6: |- ( ( ph /\ k e. A ) -> ( x e. X |-> B ) e. ( J Cn K ) )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint J k
  disjoint J x
  disjoint k ph
  disjoint ph x
  disjoint K k
  disjoint K x
  disjoint X k
  disjoint X x
  disjoint B y
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J v
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint L k
  disjoint L z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  assert |- ( ph -> ( x e. X |-> sum_ k e. A B ) e. ( J Cn K ) )

  proof
    wph
    cA
    cA
    wss
    #
    vx
    cX
    cA
    cB
    vk
    csu
    #
    cmpt
    #
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    cA
    ssid
    cA
    cfn
    wcel
    #
    wph
    @0
    @4
    wi
    #
    fsumcn.5
    wph
    vw
    cv
    #
    cA
    wss
    #
    vx
    cX
    @7
    cB
    vk
    csu
    #
    cmpt
    #
    @3
    wcel
    #
    wi
    #
    wi
    wph
    c0
    cA
    wss
    #
    vx
    cX
    c0
    cB
    vk
    csu
    #
    cmpt
    #
    @3
    wcel
    #
    wi
    #
    wi
    wph
    vy
    cv
    #
    cA
    wss
    #
    vx
    cX
    @18
    cB
    vk
    csu
    #
    cmpt
    #
    @3
    wcel
    #
    wi
    #
    wi
    wph
    @18
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
    vx
    cX
    @26
    cB
    vk
    csu
    #
    cmpt
    #
    @3
    wcel
    #
    wi
    #
    wi
    wph
    @6
    wi
    vw
    vy
    vz
    cA
    @7
    c0
    wceq
    #
    @12
    @17
    wph
    @32
    @8
    @13
    @11
    @16
    @7
    c0
    cA
    sseq1
    @32
    @10
    @15
    @3
    @32
    vx
    cX
    @9
    @14
    @7
    c0
    cB
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    vw
    vy
    weq
    #
    @12
    @23
    wph
    @33
    @8
    @19
    @11
    @22
    @7
    @18
    cA
    sseq1
    @33
    @10
    @21
    @3
    @33
    vx
    cX
    @9
    @20
    @7
    @18
    cB
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    @7
    @26
    wceq
    #
    @12
    @31
    wph
    @34
    @8
    @27
    @11
    @30
    @7
    @26
    cA
    sseq1
    @34
    @10
    @29
    @3
    @34
    vx
    cX
    @9
    @28
    @7
    @26
    cB
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    @7
    cA
    wceq
    #
    @12
    @6
    wph
    @35
    @8
    @0
    @11
    @4
    @7
    cA
    cA
    sseq1
    @35
    @10
    @2
    @3
    @35
    vx
    cX
    @9
    @1
    @7
    cA
    cB
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    wph
    @16
    @13
    wph
    @15
    vx
    cX
    cc0
    cmpt
    @3
    vx
    cX
    @14
    cc0
    cB
    vk
    sum0
    mpteq2i
    wph
    vx
    cc0
    cJ
    cK
    cX
    cc
    fsumcn.4
    cK
    cc
    ctopon
    cfv
    wcel
    #
    wph
    cK
    fsumcn.3
    cnfldtopon
    #
    a1i
    wph
    0cnd
    cnmptc
    syl5eqel
    a1d
    @18
    cfn
    wcel
    #
    @24
    @18
    wcel
    wn
    #
    wa
    wph
    @23
    @31
    @39
    wph
    @23
    @31
    wi
    #
    wi
    @38
    wph
    @39
    @40
    @23
    @27
    @22
    wi
    wph
    @39
    wa
    #
    @31
    @27
    @19
    @22
    @18
    @26
    wss
    @27
    @19
    @18
    @25
    ssun1
    @18
    @26
    cA
    sstr
    mpan
    imim1i
    @41
    @27
    @22
    @30
    @41
    @27
    @22
    @30
    @41
    @27
    @22
    wa
    #
    wa
    #
    @29
    vw
    cX
    @18
    vx
    @7
    cB
    csb
    #
    vk
    csu
    #
    vk
    @24
    @44
    csb
    #
    caddc
    co
    #
    cmpt
    #
    @3
    @43
    @29
    vx
    cX
    @20
    vk
    @24
    cB
    csb
    #
    caddc
    co
    #
    cmpt
    #
    @48
    @41
    @27
    @29
    @51
    wceq
    @22
    @41
    @27
    wa
    #
    vx
    cX
    @28
    @50
    @41
    @27
    vx
    cv
    cX
    wcel
    #
    @28
    @50
    wceq
    @41
    @27
    @53
    wa
    #
    wa
    #
    @28
    @20
    @25
    cB
    vk
    csu
    #
    caddc
    co
    @50
    @55
    @18
    @25
    cB
    @26
    vk
    @55
    @39
    @18
    @25
    cin
    c0
    wceq
    wph
    @39
    @54
    simplr
    @18
    @24
    disjsn
    sylibr
    @55
    @26
    eqidd
    @55
    @5
    @27
    @26
    cfn
    wcel
    wph
    @5
    @39
    @54
    fsumcn.5
    ad2antrr
    @41
    @27
    @53
    simprl
    #
    cA
    @26
    ssfi
    syl2anc
    @55
    vk
    cv
    #
    @26
    wcel
    #
    wa
    wph
    @58
    cA
    wcel
    #
    @53
    cB
    cc
    wcel
    #
    wph
    @39
    @54
    @59
    simplll
    @55
    @26
    cA
    @58
    @57
    sselda
    @41
    @27
    @53
    @59
    simplrr
    wph
    @60
    wa
    #
    @53
    @61
    @62
    @61
    vx
    cX
    wral
    #
    @53
    @61
    wi
    @62
    cX
    cc
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @63
    @62
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @36
    @64
    @3
    wcel
    #
    @65
    wph
    @66
    @60
    fsumcn.4
    adantr
    @36
    @62
    @37
    a1i
    fsumcn.6
    @64
    cJ
    cK
    cX
    cc
    cnf2
    syl3anc
    vx
    cX
    cc
    cB
    @64
    @64
    eqid
    fmpt
    sylibr
    @61
    vx
    cX
    rsp
    syl
    #
    imp
    syl21anc
    fsumsplit
    @55
    @56
    @49
    @20
    caddc
    @55
    @24
    cA
    wcel
    #
    @49
    cc
    wcel
    #
    @56
    @49
    wceq
    @41
    @27
    @69
    @53
    @52
    @25
    cA
    wss
    @69
    @52
    @18
    @25
    cA
    @41
    @27
    simpr
    unssbd
    @24
    cA
    vz
    vex
    snss
    sylibr
    #
    adantrr
    #
    @55
    @69
    @61
    vk
    cA
    wral
    #
    @70
    @72
    wph
    @53
    @73
    @39
    @27
    wph
    @53
    wa
    @61
    vk
    cA
    wph
    @60
    @53
    @61
    @68
    impancom
    ralrimiv
    ad2ant2rl
    @61
    @70
    vk
    @24
    cA
    vk
    @49
    cc
    vk
    @24
    cB
    nfcsb1v
    #
    nfel1
    vk
    vz
    weq
    #
    cB
    @49
    cc
    vk
    @24
    cB
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    cB
    vk
    @24
    cA
    sumsns
    syl2anc
    oveq2d
    eqtrd
    anassrs
    mpteq2dva
    adantrr
    vx
    vw
    cX
    @50
    @47
    vw
    @50
    nfcv
    vx
    @45
    @46
    caddc
    vx
    @18
    @44
    vk
    vx
    @18
    nfcv
    vx
    @7
    cB
    nfcsb1v
    #
    nfsum
    #
    vx
    caddc
    nfcv
    vx
    vk
    @24
    @44
    vx
    @24
    nfcv
    @77
    nfcsb
    #
    nfov
    vx
    vw
    weq
    #
    @20
    @45
    @49
    @46
    caddc
    @80
    @18
    cB
    @44
    vk
    vx
    @7
    cB
    csbeq1a
    #
    sumeq2sdv
    #
    @80
    vk
    @24
    cB
    @44
    @81
    csbeq2dv
    #
    oveq12d
    cbvmpt
    syl6eq
    @43
    vw
    @45
    @46
    caddc
    cJ
    cK
    cK
    cK
    cX
    wph
    @66
    @39
    @42
    fsumcn.4
    ad2antrr
    @43
    vw
    cX
    @45
    cmpt
    @21
    @3
    vx
    vw
    cX
    @20
    @45
    vw
    @20
    nfcv
    @78
    @82
    cbvmpt
    @41
    @27
    @22
    simprr
    syl5eqelr
    @43
    vw
    cX
    @46
    cmpt
    vx
    cX
    @49
    cmpt
    #
    @3
    vx
    vw
    cX
    @49
    @46
    vw
    @49
    nfcv
    @79
    @83
    cbvmpt
    @43
    @69
    @67
    vk
    cA
    wral
    #
    @84
    @3
    wcel
    #
    @41
    @27
    @69
    @22
    @71
    adantrr
    wph
    @85
    @39
    @42
    wph
    @67
    vk
    cA
    fsumcn.6
    ralrimiva
    ad2antrr
    @67
    @86
    vk
    @24
    cA
    vk
    @84
    @3
    vk
    vx
    cX
    @49
    vk
    cX
    nfcv
    @74
    nfmpt
    nfel1
    @75
    @64
    @84
    @3
    @75
    vx
    cX
    cB
    @49
    @76
    mpteq2dv
    eleq1d
    rspc
    sylc
    syl5eqelr
    caddc
    cK
    cK
    ctx
    co
    cK
    ccn
    co
    wcel
    @43
    cK
    fsumcn.3
    addcn
    a1i
    cnmpt12f
    eqeltrd
    exp32
    a2d
    syl5
    expcom
    adantl
    a2d
    findcard2s
    mpcom
    mpi
end
