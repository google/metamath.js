include "wss.mm"
include "csu.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "ssid.mm"
include "cfn.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cr.mm"
include "cc.mm"
include "0cn.mm"
include "o1const.mm"
include "sylancl.mm"
include "a1d.mm"
include "wn.mm"
include "wa.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cin.mm"
include "simprl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "adantr.mm"
include "eqidd.mm"
include "simprr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "sselda.mm"
include "adantlr.mm"
include "anass1rs.mm"
include "o1mptrcl.mm"
include "an32s.mm"
include "adantllr.mm"
include "syldan.mm"
include "fsumsplit.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "rspc.mm"
include "sylc.mm"
include "csbeq1.mm"
include "sumsn.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "reex.mm"
include "ssex.mm"
include "syl.mm"
include "sumex.mm"
include "a1i.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "id.mm"
include "nfmpt.mm"
include "o1add.mm"
include "syl2anr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fsumo1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume fsumo1.1: |- ( ph -> A C_ RR )
  assume fsumo1.2: |- ( ph -> B e. Fin )
  assume fsumo1.3: |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> C e. V )
  assume fsumo1.4: |- ( ( ph /\ k e. B ) -> ( x e. A |-> C ) e. O(1) )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint B x
  disjoint k ph
  disjoint ph x
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( x e. A |-> sum_ k e. B C ) e. O(1) )

  proof
    wph
    cB
    cB
    wss
    #
    vx
    cA
    cB
    cC
    vk
    csu
    #
    cmpt
    #
    co1
    wcel
    #
    cB
    ssid
    cB
    cfn
    wcel
    #
    wph
    @0
    @3
    wi
    #
    fsumo1.2
    wph
    vw
    cv
    #
    cB
    wss
    #
    vx
    cA
    @6
    cC
    vk
    csu
    #
    cmpt
    #
    co1
    wcel
    #
    wi
    #
    wi
    wph
    c0
    cB
    wss
    #
    vx
    cA
    cc0
    cmpt
    #
    co1
    wcel
    #
    wi
    #
    wi
    wph
    vy
    cv
    #
    cB
    wss
    #
    vx
    cA
    @16
    cC
    vk
    csu
    #
    cmpt
    #
    co1
    wcel
    #
    wi
    #
    wi
    #
    wph
    @16
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    wss
    #
    vx
    cA
    @25
    cC
    vk
    csu
    #
    cmpt
    #
    co1
    wcel
    #
    wi
    #
    wi
    #
    wph
    @5
    wi
    vw
    vy
    vz
    cB
    @6
    c0
    wceq
    #
    @11
    @15
    wph
    @32
    @7
    @12
    @10
    @14
    @6
    c0
    cB
    sseq1
    @32
    @9
    @13
    co1
    @32
    vx
    cA
    @8
    cc0
    @32
    @8
    c0
    cC
    vk
    csu
    cc0
    @6
    c0
    cC
    vk
    sumeq1
    cC
    vk
    sum0
    syl6eq
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    @6
    @16
    wceq
    #
    @11
    @21
    wph
    @33
    @7
    @17
    @10
    @20
    @6
    @16
    cB
    sseq1
    @33
    @9
    @19
    co1
    @33
    vx
    cA
    @8
    @18
    @6
    @16
    cC
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    @6
    @25
    wceq
    #
    @11
    @30
    wph
    @34
    @7
    @26
    @10
    @29
    @6
    @25
    cB
    sseq1
    @34
    @9
    @28
    co1
    @34
    vx
    cA
    @8
    @27
    @6
    @25
    cC
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    @6
    cB
    wceq
    #
    @11
    @5
    wph
    @35
    @7
    @0
    @10
    @3
    @6
    cB
    cB
    sseq1
    @35
    @9
    @2
    co1
    @35
    vx
    cA
    @8
    @1
    @6
    cB
    cC
    vk
    sumeq1
    mpteq2dv
    eleq1d
    imbi12d
    imbi2d
    wph
    @14
    @12
    wph
    cA
    cr
    wss
    #
    cc0
    cc
    wcel
    @14
    fsumo1.1
    0cn
    vx
    cA
    cc0
    o1const
    sylancl
    a1d
    @23
    @16
    wcel
    wn
    #
    @22
    @31
    wi
    @16
    cfn
    wcel
    @37
    wph
    @21
    @30
    wph
    @37
    @21
    @30
    wi
    @21
    @26
    @20
    wi
    wph
    @37
    wa
    #
    @30
    @26
    @17
    @20
    @16
    @25
    wss
    @26
    @17
    @16
    @24
    ssun1
    @16
    @25
    cB
    sstr
    mpan
    imim1i
    @38
    @26
    @20
    @29
    wph
    @37
    @26
    @20
    @29
    wi
    wph
    @37
    @26
    wa
    #
    wa
    #
    @20
    @29
    @40
    @20
    wa
    @28
    @19
    vx
    cA
    vk
    @23
    cC
    csb
    #
    cmpt
    #
    caddc
    cof
    co
    #
    co1
    @40
    @28
    @43
    wceq
    @20
    @40
    @28
    vx
    cA
    @18
    @41
    caddc
    co
    #
    cmpt
    @43
    @40
    vx
    cA
    @27
    @44
    @40
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @27
    @18
    @24
    cC
    vk
    csu
    #
    caddc
    co
    @44
    @46
    @16
    @24
    cC
    @25
    vk
    @40
    @16
    @24
    cin
    c0
    wceq
    #
    @45
    @40
    @37
    @48
    wph
    @37
    @26
    simprl
    @16
    @23
    disjsn
    sylibr
    adantr
    @46
    @25
    eqidd
    @40
    @25
    cfn
    wcel
    #
    @45
    @40
    @4
    @26
    @49
    wph
    @4
    @39
    fsumo1.2
    adantr
    wph
    @37
    @26
    simprr
    #
    cB
    @25
    ssfi
    syl2anc
    adantr
    @46
    vk
    cv
    #
    @25
    wcel
    #
    @51
    cB
    wcel
    #
    cC
    cc
    wcel
    #
    @40
    @52
    @53
    @45
    @40
    @25
    cB
    @51
    @50
    sselda
    adantlr
    wph
    @45
    @53
    @54
    @39
    wph
    @53
    @45
    @54
    wph
    @53
    wa
    vx
    cA
    cC
    cV
    wph
    @45
    @53
    cC
    cV
    wcel
    fsumo1.3
    anass1rs
    fsumo1.4
    o1mptrcl
    an32s
    adantllr
    #
    syldan
    fsumsplit
    @46
    @47
    @41
    @18
    caddc
    @46
    @47
    @24
    vk
    @6
    cC
    csb
    #
    vw
    csu
    #
    @41
    @24
    cC
    @56
    vk
    vw
    vw
    cC
    nfcv
    vk
    @6
    cC
    nfcsb1v
    vk
    @6
    cC
    csbeq1a
    cbvsumi
    @46
    @23
    cB
    wcel
    #
    @41
    cc
    wcel
    #
    @57
    @41
    wceq
    @40
    @58
    @45
    @40
    @24
    cB
    wss
    @58
    @40
    @16
    @24
    cB
    @50
    unssbd
    @23
    cB
    vz
    vex
    snss
    sylibr
    #
    adantr
    #
    @46
    @58
    @54
    vk
    cB
    wral
    @59
    @61
    @46
    @54
    vk
    cB
    @55
    ralrimiva
    @54
    @59
    vk
    @23
    cB
    vk
    @41
    cc
    vk
    @23
    cC
    nfcsb1v
    #
    nfel1
    @51
    @23
    wceq
    #
    cC
    @41
    cc
    vk
    @23
    cC
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    #
    @56
    @41
    vw
    @23
    cB
    vk
    @6
    @23
    cC
    csbeq1
    sumsn
    syl2anc
    syl5eq
    oveq2d
    eqtrd
    mpteq2dva
    @40
    vx
    cA
    @18
    @41
    caddc
    @19
    @42
    cvv
    cvv
    cc
    @40
    @36
    cA
    cvv
    wcel
    wph
    @36
    @39
    fsumo1.1
    adantr
    cA
    cr
    reex
    ssex
    syl
    @18
    cvv
    wcel
    @46
    @16
    cC
    vk
    sumex
    a1i
    @65
    @40
    @19
    eqidd
    @40
    @42
    eqidd
    offval2
    eqtr4d
    adantr
    @20
    @20
    @42
    co1
    wcel
    #
    @43
    co1
    wcel
    @40
    @20
    id
    @40
    @58
    vx
    cA
    cC
    cmpt
    #
    co1
    wcel
    #
    vk
    cB
    wral
    #
    @66
    @60
    wph
    @69
    @39
    wph
    @68
    vk
    cB
    fsumo1.4
    ralrimiva
    adantr
    @68
    @66
    vk
    @23
    cB
    vk
    @42
    co1
    vk
    vx
    cA
    @41
    vk
    cA
    nfcv
    @62
    nfmpt
    nfel1
    @63
    @67
    @42
    co1
    @63
    vx
    cA
    cC
    @41
    @64
    mpteq2dv
    eleq1d
    rspc
    sylc
    @19
    @42
    o1add
    syl2anr
    eqeltrd
    ex
    expr
    a2d
    syl5
    expcom
    a2d
    adantl
    findcard2s
    mpcom
    mpi
end
