include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cxad.mm"
include "nfv.mm"
include "sge0revalmpt.mm"
include "oveq12d.mm"
include "cr.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "readdcld.mm"
include "rexrd.mm"
include "wss.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "elinel2.mm"
include "adantl.mm"
include "simpll.mm"
include "elpwinss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantll.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "sseldi.mm"
include "syl2anc.mm"
include "fsumrecl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "supxrcl.mm"
include "rpxrd.mm"
include "xaddcld.mm"
include "c2.mm"
include "cdiv.mm"
include "simpl.mm"
include "sselda.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "a1i.mm"
include "ltadd12dd.mm"
include "cle.mm"
include "recnd.mm"
include "add4d.mm"
include "2halvesd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wceq.mm"
include "wbr.mm"
include "pnfxr.mm"
include "ltpnf.mm"
include "xrltled.mm"
include "oveq1.mm"
include "cmnf.mm"
include "wne.mm"
include "renemnfd.mm"
include "xaddpnf2.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "wn.mm"
include "cicc.mm"
include "neqne.mm"
include "ge0xrre.mm"
include "cun.mm"
include "jca.mm"
include "unfi.mm"
include "unssd.mm"
include "syldan.mm"
include "icossicc.mm"
include "xrge0ge0.mm"
include "ssun1.mm"
include "fsumless.mm"
include "ssun2.mm"
include "leadd12dd.mm"
include "fsumadd.mm"
include "cvv.mm"
include "elpwd.mm"
include "elind.mm"
include "elexd.mm"
include "sumeq1.mm"
include "elrnmpt1s.mm"
include "supxrub.mm"
include "letrd.mm"
include "leadd1dd.mm"
include "rexadd.mm"
include "pm2.61dan.mm"
include "eqbrtrd.mm"
include "xrltletrd.mm"

theorem sge0xaddlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z
  assume sge0xaddlem1.a: |- ( ph -> A e. V )
  assume sge0xaddlem1.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )
  assume sge0xaddlem1.c: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,) +oo ) )
  assume sge0xaddlem1.rp: |- ( ph -> E e. RR+ )
  assume sge0xaddlem1.u: |- ( ph -> U C_ A )
  assume sge0xaddlem1.ufi: |- ( ph -> U e. Fin )
  assume sge0xaddlem1.7: |- ( ph -> W C_ A )
  assume sge0xaddlem1.wfi: |- ( ph -> W e. Fin )
  assume sge0xaddlem1.ltb: |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) < ( sum_ k e. U B + ( E / 2 ) ) )
  assume sge0xaddlem1.ltc: |- ( ph -> ( sum^ ` ( k e. A |-> C ) ) < ( sum_ k e. W C + ( E / 2 ) ) )
  assume sge0xaddlem1.xr: |- ( ph -> sup ( ran ( x e. ( ~P A i^i Fin ) |-> sum_ k e. x ( B + C ) ) , RR* , < ) e. ( 0 [,] +oo ) )
  assume sge0xaddlem1.sb: |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) e. RR )
  assume sge0xaddlem1.sc: |- ( ph -> ( sum^ ` ( k e. A |-> C ) ) e. RR )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint C x
  disjoint U k
  disjoint U x
  disjoint W k
  disjoint W x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A y
  disjoint k y
  disjoint A z
  disjoint k z
  disjoint B y
  disjoint C z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( ( sum^ ` ( k e. A |-> B ) ) + ( sum^ ` ( k e. A |-> C ) ) ) <_ ( sup ( ran ( x e. ( ~P A i^i Fin ) |-> sum_ k e. x ( B + C ) ) , RR* , < ) +e E ) )

  proof
    wph
    vk
    cA
    cB
    cmpt
    csumge0
    cfv
    #
    vk
    cA
    cC
    cmpt
    csumge0
    cfv
    #
    caddc
    co
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    cB
    cC
    caddc
    co
    #
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cE
    cxad
    co
    #
    wph
    @2
    vy
    @4
    vy
    cv
    cB
    vk
    csu
    cmpt
    crn
    cxr
    clt
    csup
    #
    vz
    @4
    vz
    cv
    cC
    vk
    csu
    cmpt
    crn
    cxr
    clt
    csup
    #
    caddc
    co
    #
    cxr
    wph
    @0
    @12
    @1
    @13
    caddc
    wph
    vk
    vy
    cA
    cB
    cV
    wph
    vk
    nfv
    #
    sge0xaddlem1.a
    sge0xaddlem1.b
    sge0revalmpt
    #
    wph
    vk
    vz
    cA
    cC
    cV
    @15
    sge0xaddlem1.a
    sge0xaddlem1.c
    sge0revalmpt
    #
    oveq12d
    wph
    @14
    wph
    @12
    @13
    wph
    @12
    @0
    cr
    wph
    @0
    @12
    @16
    eqcomd
    sge0xaddlem1.sb
    eqeltrd
    wph
    @1
    @13
    cr
    @17
    sge0xaddlem1.sc
    eqeltrrd
    readdcld
    rexrd
    eqeltrd
    #
    wph
    @10
    cE
    wph
    @9
    cxr
    wss
    #
    @10
    cxr
    wcel
    wph
    @7
    cxr
    wcel
    #
    vx
    @4
    wral
    @19
    wph
    @20
    vx
    @4
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @7
    @22
    @5
    @6
    vk
    @21
    @5
    cfn
    wcel
    wph
    @5
    @3
    cfn
    elinel2
    adantl
    @22
    vk
    cv
    #
    @5
    wcel
    #
    wa
    #
    cB
    cC
    @25
    wph
    @23
    cA
    wcel
    #
    cB
    cr
    wcel
    #
    wph
    @21
    @24
    simpll
    #
    @21
    @24
    @26
    wph
    @21
    @24
    wa
    @5
    cA
    @23
    @21
    @5
    cA
    wss
    @24
    @5
    cA
    cfn
    elpwinss
    adantr
    @21
    @24
    simpr
    sseldd
    adantll
    #
    wph
    @26
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    cB
    rge0ssre
    sge0xaddlem1.b
    sseldi
    #
    syl2anc
    @25
    wph
    @26
    cC
    cr
    wcel
    #
    @28
    @29
    @30
    @31
    cr
    cC
    rge0ssre
    sge0xaddlem1.c
    sseldi
    #
    syl2anc
    readdcld
    fsumrecl
    rexrd
    ralrimiva
    vx
    @4
    @7
    cxr
    @8
    @8
    eqid
    #
    rnmptss
    syl
    #
    @9
    supxrcl
    syl
    wph
    cE
    sge0xaddlem1.rp
    rpxrd
    #
    xaddcld
    #
    wph
    @2
    cU
    cB
    vk
    csu
    #
    cE
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cW
    cC
    vk
    csu
    #
    @40
    caddc
    co
    #
    caddc
    co
    #
    @11
    @18
    wph
    @44
    wph
    @41
    @43
    wph
    @39
    @40
    wph
    cU
    cB
    vk
    sge0xaddlem1.ufi
    wph
    @23
    cU
    wcel
    #
    wa
    #
    @31
    cr
    cB
    rge0ssre
    @46
    wph
    @26
    cB
    @31
    wcel
    wph
    @45
    simpl
    wph
    cU
    cA
    @23
    sge0xaddlem1.u
    sselda
    sge0xaddlem1.b
    syl2anc
    sseldi
    fsumrecl
    #
    wph
    cE
    wph
    cE
    sge0xaddlem1.rp
    rpred
    #
    rehalfcld
    #
    readdcld
    #
    wph
    @42
    @40
    wph
    cW
    cC
    vk
    sge0xaddlem1.wfi
    wph
    @23
    cW
    wcel
    #
    wa
    #
    @31
    cr
    cC
    @31
    cr
    wss
    @52
    rge0ssre
    a1i
    @52
    wph
    @26
    cC
    @31
    wcel
    wph
    @51
    simpl
    @52
    cW
    cA
    @23
    wph
    cW
    cA
    wss
    @51
    sge0xaddlem1.7
    adantr
    wph
    @51
    simpr
    sseldd
    sge0xaddlem1.c
    syl2anc
    sseldd
    fsumrecl
    #
    @49
    readdcld
    #
    readdcld
    #
    rexrd
    #
    @38
    wph
    @0
    @1
    @41
    @43
    sge0xaddlem1.sb
    sge0xaddlem1.sc
    @50
    @54
    sge0xaddlem1.ltb
    sge0xaddlem1.ltc
    ltadd12dd
    wph
    @44
    @39
    @42
    caddc
    co
    #
    cE
    caddc
    co
    #
    @11
    cle
    wph
    @44
    @57
    @40
    @40
    caddc
    co
    #
    caddc
    co
    @58
    wph
    @39
    @40
    @42
    @40
    wph
    @39
    @47
    recnd
    wph
    @40
    @49
    recnd
    #
    wph
    @42
    @53
    recnd
    @60
    add4d
    wph
    @59
    cE
    @57
    caddc
    wph
    cE
    wph
    cE
    @48
    recnd
    2halvesd
    oveq2d
    eqtrd
    #
    wph
    @10
    cpnf
    wceq
    #
    @58
    @11
    cle
    wbr
    #
    wph
    @62
    wa
    #
    @58
    cpnf
    @11
    cle
    wph
    @58
    cpnf
    cle
    wbr
    @62
    wph
    @58
    cpnf
    wph
    @44
    @58
    cxr
    @61
    @56
    eqeltrrd
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    @58
    cr
    wcel
    @58
    cpnf
    clt
    wbr
    wph
    @44
    @58
    cr
    @61
    @55
    eqeltrrd
    @58
    ltpnf
    syl
    xrltled
    adantr
    @64
    @11
    cpnf
    cE
    cxad
    co
    #
    cpnf
    @62
    @11
    @65
    wceq
    wph
    @10
    cpnf
    cE
    cxad
    oveq1
    adantl
    wph
    @65
    cpnf
    wceq
    #
    @62
    wph
    cE
    cxr
    wcel
    cE
    cmnf
    wne
    @66
    @37
    wph
    cE
    @48
    renemnfd
    cE
    xaddpnf2
    syl2anc
    adantr
    eqtr2d
    breqtrd
    wph
    @62
    wn
    #
    wa
    #
    wph
    @10
    cr
    wcel
    #
    @63
    wph
    @67
    simpl
    #
    @68
    @10
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @10
    cpnf
    wne
    #
    @69
    @68
    wph
    @72
    @70
    sge0xaddlem1.xr
    syl
    @67
    @73
    wph
    @10
    cpnf
    neqne
    adantl
    @10
    ge0xrre
    syl2anc
    wph
    @69
    wa
    #
    @58
    @10
    cE
    caddc
    co
    #
    @11
    cle
    @74
    @57
    @10
    cE
    wph
    @57
    cr
    wcel
    @69
    wph
    @39
    @42
    @47
    @53
    readdcld
    adantr
    #
    wph
    @69
    simpr
    #
    wph
    cE
    cr
    wcel
    #
    @69
    @48
    adantr
    #
    @74
    @57
    cU
    cW
    cun
    #
    @6
    vk
    csu
    #
    @10
    @76
    wph
    @81
    cr
    wcel
    @69
    wph
    @80
    @6
    vk
    wph
    cU
    cfn
    wcel
    #
    cW
    cfn
    wcel
    #
    wa
    @80
    cfn
    wcel
    wph
    @82
    @83
    sge0xaddlem1.ufi
    sge0xaddlem1.wfi
    jca
    cU
    cW
    unfi
    syl
    #
    wph
    @23
    @80
    wcel
    #
    wa
    #
    cB
    cC
    @86
    wph
    @26
    @27
    wph
    @85
    simpl
    @86
    @80
    cA
    @23
    wph
    @80
    cA
    wss
    @85
    wph
    cU
    cW
    cA
    sge0xaddlem1.u
    sge0xaddlem1.7
    unssd
    #
    adantr
    wph
    @85
    simpr
    sseldd
    #
    @32
    syl2anc
    #
    wph
    @85
    @26
    @33
    @88
    @34
    syldan
    #
    readdcld
    fsumrecl
    #
    adantr
    @77
    wph
    @57
    @81
    cle
    wbr
    @69
    wph
    @57
    @80
    cB
    vk
    csu
    #
    @80
    cC
    vk
    csu
    #
    caddc
    co
    #
    @81
    cle
    wph
    @39
    @42
    @92
    @93
    @47
    @53
    wph
    @80
    cB
    vk
    @84
    @89
    fsumrecl
    wph
    @80
    cC
    vk
    @84
    @90
    fsumrecl
    wph
    @80
    cB
    cU
    vk
    @84
    @89
    wph
    @85
    @26
    cc0
    cB
    cle
    wbr
    #
    @88
    @30
    cB
    @71
    wcel
    @95
    @30
    @31
    @71
    cB
    cc0
    cpnf
    icossicc
    #
    sge0xaddlem1.b
    sseldi
    cB
    xrge0ge0
    syl
    syldan
    cU
    @80
    wss
    wph
    cU
    cW
    ssun1
    a1i
    fsumless
    wph
    @80
    cC
    cW
    vk
    @84
    @90
    wph
    @85
    @26
    cc0
    cC
    cle
    wbr
    #
    @88
    @30
    cC
    @71
    wcel
    @97
    @30
    @31
    @71
    cC
    @96
    sge0xaddlem1.c
    sseldi
    cC
    xrge0ge0
    syl
    syldan
    cW
    @80
    wss
    wph
    cW
    cU
    ssun2
    a1i
    fsumless
    leadd12dd
    wph
    @81
    @94
    wph
    @80
    cB
    cC
    vk
    @84
    @86
    cB
    @89
    recnd
    @86
    cC
    @90
    recnd
    fsumadd
    eqcomd
    breqtrd
    adantr
    @74
    @19
    @81
    @9
    wcel
    #
    @81
    @10
    cle
    wbr
    wph
    @19
    @69
    @36
    adantr
    wph
    @98
    @69
    wph
    @80
    @4
    wcel
    @81
    cvv
    wcel
    @98
    wph
    @3
    cfn
    @80
    wph
    @80
    cA
    cfn
    @84
    @87
    elpwd
    @84
    elind
    wph
    @81
    cr
    @91
    elexd
    vx
    @4
    @7
    @81
    @80
    @8
    cvv
    @35
    @5
    @80
    @6
    vk
    sumeq1
    elrnmpt1s
    syl2anc
    adantr
    @9
    @81
    supxrub
    syl2anc
    letrd
    leadd1dd
    @74
    @11
    @75
    @74
    @69
    @78
    @11
    @75
    wceq
    @77
    @79
    @10
    cE
    rexadd
    syl2anc
    eqcomd
    breqtrd
    syl2anc
    pm2.61dan
    eqbrtrd
    xrltletrd
    xrltled
end
