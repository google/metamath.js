include "cv.mm"
include "cprod.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "prodeq1.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "c1.mm"
include "prod0.mm"
include "a1i.mm"
include "1cnd.mm"
include "wss.mm"
include "ssid.mm"
include "constcncfg.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "wa.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcprod.mm"
include "csbeq1a.mm"
include "adantr.mm"
include "prodeq2dv.mm"
include "cbvmpt.mm"
include "cmul.mm"
include "cvv.mm"
include "nfv.mm"
include "cfn.mm"
include "simpr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "vex.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antll.mm"
include "simplll.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "w3a.mm"
include "wi.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "syl3anc.mm"
include "simpll.mm"
include "eldifi.mm"
include "nfel.mm"
include "3anbi3d.mm"
include "syl21anc.mm"
include "fprodsplitsn.mm"
include "mpteq2dva.mm"
include "eqcomi.mm"
include "id.mm"
include "adantl.mm"
include "nfmpt.mm"
include "anbi2d.mm"
include "syl5eqelr.mm"
include "syldan.mm"
include "mulcncf.mm"
include "ex.mm"
include "findcard2d.mm"

theorem fprodcncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume fprodcncf.a: |- ( ph -> A C_ CC )
  assume fprodcncf.b: |- ( ph -> B e. Fin )
  assume fprodcncf.c: |- ( ( ph /\ x e. A /\ k e. B ) -> C e. CC )
  assume fprodcncf.cn: |- ( ( ph /\ k e. B ) -> ( x e. A |-> C ) e. ( A -cn-> CC ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A u
  disjoint A y
  disjoint A z
  disjoint k u
  disjoint k y
  disjoint k z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint k w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B u
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C u
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint ph w
  assert |- ( ph -> ( x e. A |-> prod_ k e. B C ) e. ( A -cn-> CC ) )

  proof
    wph
    vx
    cA
    vw
    cv
    #
    cC
    vk
    cprod
    #
    cmpt
    #
    cA
    cc
    ccncf
    co
    #
    wcel
    vx
    cA
    c0
    cC
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    vx
    cA
    vz
    cv
    #
    cC
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    #
    vx
    cA
    @6
    vy
    cv
    #
    csn
    cun
    #
    cC
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    #
    vx
    cA
    cB
    cC
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    vw
    vz
    vy
    cB
    @0
    c0
    wceq
    #
    @2
    @5
    @3
    @17
    vx
    cA
    @1
    @4
    @0
    c0
    cC
    vk
    prodeq1
    mpteq2dv
    eleq1d
    @0
    @6
    wceq
    #
    @2
    @8
    @3
    @18
    vx
    cA
    @1
    @7
    @0
    @6
    cC
    vk
    prodeq1
    mpteq2dv
    eleq1d
    @0
    @11
    wceq
    #
    @2
    @13
    @3
    @19
    vx
    cA
    @1
    @12
    @0
    @11
    cC
    vk
    prodeq1
    mpteq2dv
    eleq1d
    @0
    cB
    wceq
    #
    @2
    @16
    @3
    @20
    vx
    cA
    @1
    @15
    @0
    cB
    cC
    vk
    prodeq1
    mpteq2dv
    eleq1d
    wph
    @5
    vx
    cA
    c1
    cmpt
    @3
    wph
    vx
    cA
    @4
    c1
    @4
    c1
    wceq
    wph
    cC
    vk
    prod0
    a1i
    mpteq2dv
    wph
    vx
    cA
    c1
    cc
    fprodcncf.a
    wph
    1cnd
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    constcncfg
    eqeltrd
    wph
    @6
    cB
    wss
    #
    @10
    cB
    @6
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @9
    @14
    @24
    @9
    wa
    #
    @13
    vu
    cA
    @11
    vx
    vu
    cv
    #
    cC
    csb
    #
    vk
    cprod
    #
    cmpt
    #
    @3
    @13
    @29
    wceq
    @25
    vx
    vu
    cA
    @12
    @28
    vu
    @12
    nfcv
    vx
    @11
    @27
    vk
    vx
    @11
    nfcv
    vx
    @26
    cC
    nfcsb1v
    #
    nfcprod
    vx
    cv
    #
    @26
    wceq
    #
    @11
    cC
    @27
    vk
    @32
    cC
    @27
    wceq
    #
    vk
    cv
    #
    @11
    wcel
    vx
    @26
    cC
    csbeq1a
    #
    adantr
    prodeq2dv
    cbvmpt
    a1i
    @25
    @29
    vu
    cA
    @6
    @27
    vk
    cprod
    #
    vk
    @10
    @27
    csb
    #
    cmul
    co
    #
    cmpt
    #
    @3
    @24
    @29
    @39
    wceq
    @9
    @24
    vu
    cA
    @28
    @38
    @24
    @26
    cA
    wcel
    #
    wa
    #
    @6
    @10
    @27
    @37
    vk
    cvv
    @41
    vk
    nfv
    vk
    @10
    @27
    nfcsb1v
    #
    @24
    @6
    cfn
    wcel
    #
    @40
    wph
    @21
    @43
    @22
    wph
    @21
    wa
    cB
    cfn
    wcel
    #
    @21
    @43
    wph
    @44
    @21
    fprodcncf.b
    adantr
    wph
    @21
    simpr
    #
    cB
    @6
    ssfi
    syl2anc
    adantrr
    adantr
    @10
    cvv
    wcel
    @41
    vy
    vex
    a1i
    @24
    @10
    @6
    wcel
    wn
    #
    @40
    @22
    @46
    wph
    @21
    @10
    cB
    @6
    eldifn
    ad2antll
    adantr
    @41
    @34
    @6
    wcel
    #
    wa
    #
    wph
    @40
    @34
    cB
    wcel
    #
    @27
    cc
    wcel
    #
    wph
    @23
    @40
    @47
    simplll
    @24
    @40
    @47
    simplr
    @48
    @6
    cB
    @34
    @24
    @21
    @40
    @47
    wph
    @21
    @21
    @22
    @45
    adantrr
    ad2antrr
    @41
    @47
    simpr
    sseldd
    wph
    @31
    cA
    wcel
    #
    @49
    w3a
    #
    cC
    cc
    wcel
    #
    wi
    wph
    @40
    @49
    w3a
    #
    @50
    wi
    #
    vx
    vu
    @54
    @50
    vx
    @54
    vx
    nfv
    vx
    @27
    cc
    @30
    nfel1
    nfim
    @32
    @52
    @54
    @53
    @50
    @32
    @51
    @40
    wph
    @49
    @31
    @26
    cA
    eleq1
    3anbi2d
    @32
    cC
    @27
    cc
    @35
    eleq1d
    imbi12d
    fprodcncf.c
    chvar
    #
    syl3anc
    vk
    @10
    @27
    csbeq1a
    #
    @41
    wph
    @10
    cB
    wcel
    #
    @40
    @37
    cc
    wcel
    #
    wph
    @23
    @40
    simpll
    @24
    @58
    @40
    @22
    @58
    wph
    @21
    @10
    cB
    @6
    eldifi
    ad2antll
    #
    adantr
    @24
    @40
    simpr
    wph
    @58
    wa
    #
    @40
    wa
    wph
    @40
    @58
    @59
    wph
    @58
    @40
    simpll
    @61
    @40
    simpr
    wph
    @58
    @40
    simplr
    @55
    wph
    @40
    @58
    w3a
    #
    @59
    wi
    vk
    vy
    @62
    @59
    vk
    @62
    vk
    nfv
    vk
    @37
    cc
    @42
    vk
    cc
    nfcv
    nfel
    nfim
    @34
    @10
    wceq
    #
    @54
    @62
    @50
    @59
    @63
    @49
    @58
    wph
    @40
    @34
    @10
    cB
    eleq1
    #
    3anbi3d
    @63
    @27
    @37
    cc
    @57
    eleq1d
    imbi12d
    @56
    chvar
    syl3anc
    syl21anc
    fprodsplitsn
    mpteq2dva
    adantr
    @25
    vu
    @36
    @37
    cA
    @9
    vu
    cA
    @36
    cmpt
    #
    @3
    wcel
    @24
    @9
    @65
    @8
    @3
    @65
    @8
    wceq
    @9
    @8
    @65
    vx
    vu
    cA
    @7
    @36
    vu
    @7
    nfcv
    vx
    @6
    @27
    vk
    vx
    @6
    nfcv
    @30
    nfcprod
    @32
    @6
    cC
    @27
    vk
    @32
    @33
    @47
    @35
    adantr
    prodeq2dv
    cbvmpt
    eqcomi
    a1i
    @9
    id
    eqeltrd
    adantl
    @24
    vu
    cA
    @37
    cmpt
    #
    @3
    wcel
    #
    @9
    wph
    @23
    @58
    @67
    @60
    wph
    @49
    wa
    #
    vu
    cA
    @27
    cmpt
    #
    @3
    wcel
    #
    wi
    @61
    @67
    wi
    vk
    vy
    @61
    @67
    vk
    @61
    vk
    nfv
    vk
    @66
    @3
    vk
    vu
    cA
    @37
    vk
    cA
    nfcv
    @42
    nfmpt
    vk
    @3
    nfcv
    nfel
    nfim
    @63
    @68
    @61
    @70
    @67
    @63
    @49
    @58
    wph
    @64
    anbi2d
    @63
    @69
    @66
    @3
    @63
    vu
    cA
    @27
    @37
    @63
    @27
    @37
    wceq
    @40
    @57
    adantr
    mpteq2dva
    eleq1d
    imbi12d
    @68
    @69
    vx
    cA
    cC
    cmpt
    @3
    vx
    vu
    cA
    cC
    @27
    vu
    cC
    nfcv
    @30
    @35
    cbvmpt
    fprodcncf.cn
    syl5eqelr
    chvar
    syldan
    adantr
    mulcncf
    eqeltrd
    eqeltrd
    ex
    fprodcncf.b
    findcard2d
end
