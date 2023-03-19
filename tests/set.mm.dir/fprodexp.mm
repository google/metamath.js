include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cprod.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "prodeq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "nn0zd.mm"
include "1exp.mm"
include "syl.mm"
include "eqcomd.mm"
include "prod0.mm"
include "a1i.mm"
include "oveq1i.mm"
include "3eqtr4d.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "csb.mm"
include "cmul.mm"
include "cc.mm"
include "cn0.mm"
include "nfv.mm"
include "nfan.mm"
include "cfn.mm"
include "adantr.mm"
include "simpr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "simpll.mm"
include "sselda.mm"
include "adantlrr.mm"
include "fprodclf.mm"
include "simpl.mm"
include "simprr.mm"
include "eldifad.mm"
include "wi.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "mulexp.mm"
include "syl3anc.mm"
include "nfcv.mm"
include "nfov.mm"
include "eldifbd.mm"
include "ad2antrr.mm"
include "expcld.mm"
include "fprodsplitsn.mm"
include "oveq1.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "findcard2d.mm"

theorem fprodexp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fprodexp.kph: |- F/ k ph
  assume fprodexp.n: |- ( ph -> N e. NN0 )
  assume fprodexp.a: |- ( ph -> A e. Fin )
  assume fprodexp.b: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint N k
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> prod_ k e. A ( B ^ N ) = ( prod_ k e. A B ^ N ) )

  proof
    wph
    vx
    cv
    #
    cB
    cN
    cexp
    co
    #
    vk
    cprod
    #
    @0
    cB
    vk
    cprod
    #
    cN
    cexp
    co
    #
    wceq
    c0
    @1
    vk
    cprod
    #
    c0
    cB
    vk
    cprod
    #
    cN
    cexp
    co
    #
    wceq
    vy
    cv
    #
    @1
    vk
    cprod
    #
    @8
    cB
    vk
    cprod
    #
    cN
    cexp
    co
    #
    wceq
    #
    @8
    vz
    cv
    #
    csn
    cun
    #
    @1
    vk
    cprod
    #
    @14
    cB
    vk
    cprod
    #
    cN
    cexp
    co
    #
    wceq
    #
    cA
    @1
    vk
    cprod
    #
    cA
    cB
    vk
    cprod
    #
    cN
    cexp
    co
    #
    wceq
    vx
    vy
    vz
    cA
    @0
    c0
    wceq
    #
    @2
    @5
    @4
    @7
    @0
    c0
    @1
    vk
    prodeq1
    @22
    @3
    @6
    cN
    cexp
    @0
    c0
    cB
    vk
    prodeq1
    oveq1d
    eqeq12d
    @0
    @8
    wceq
    #
    @2
    @9
    @4
    @11
    @0
    @8
    @1
    vk
    prodeq1
    @23
    @3
    @10
    cN
    cexp
    @0
    @8
    cB
    vk
    prodeq1
    oveq1d
    eqeq12d
    @0
    @14
    wceq
    #
    @2
    @15
    @4
    @17
    @0
    @14
    @1
    vk
    prodeq1
    @24
    @3
    @16
    cN
    cexp
    @0
    @14
    cB
    vk
    prodeq1
    oveq1d
    eqeq12d
    @0
    cA
    wceq
    #
    @2
    @19
    @4
    @21
    @0
    cA
    @1
    vk
    prodeq1
    @25
    @3
    @20
    cN
    cexp
    @0
    cA
    cB
    vk
    prodeq1
    oveq1d
    eqeq12d
    wph
    c1
    c1
    cN
    cexp
    co
    #
    @5
    @7
    wph
    @26
    c1
    wph
    cN
    cz
    wcel
    @26
    c1
    wceq
    wph
    cN
    fprodexp.n
    nn0zd
    cN
    1exp
    syl
    eqcomd
    @5
    c1
    wceq
    wph
    @1
    vk
    prod0
    a1i
    @7
    @26
    wceq
    wph
    @6
    c1
    cN
    cexp
    cB
    vk
    prod0
    oveq1i
    a1i
    3eqtr4d
    wph
    @8
    cA
    wss
    #
    @13
    cA
    @8
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    @12
    @18
    @31
    @12
    wa
    #
    @11
    vk
    @13
    cB
    csb
    #
    cN
    cexp
    co
    #
    cmul
    co
    #
    @10
    @33
    cmul
    co
    #
    cN
    cexp
    co
    #
    @15
    @17
    @31
    @35
    @37
    wceq
    @12
    @31
    @37
    @35
    @31
    @10
    cc
    wcel
    @33
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    @37
    @35
    wceq
    @31
    @8
    cB
    vk
    wph
    @30
    vk
    fprodexp.kph
    @30
    vk
    nfv
    nfan
    #
    wph
    @27
    @8
    cfn
    wcel
    #
    @29
    wph
    @27
    wa
    #
    cA
    cfn
    wcel
    #
    @27
    @41
    wph
    @43
    @27
    fprodexp.a
    adantr
    wph
    @27
    simpr
    #
    cA
    @8
    ssfi
    syl2anc
    adantrr
    #
    wph
    @27
    vk
    cv
    #
    @8
    wcel
    #
    cB
    cc
    wcel
    #
    @29
    @42
    @47
    wa
    #
    wph
    @46
    cA
    wcel
    #
    @48
    wph
    @27
    @47
    simpll
    @42
    @8
    cA
    @46
    @44
    sselda
    fprodexp.b
    syl2anc
    #
    adantlrr
    #
    fprodclf
    @31
    wph
    @13
    cA
    wcel
    #
    @38
    wph
    @30
    simpl
    @31
    @13
    cA
    @8
    wph
    @27
    @29
    simprr
    #
    eldifad
    wph
    @50
    wa
    #
    @48
    wi
    wph
    @53
    wa
    #
    @38
    wi
    vk
    vz
    @56
    @38
    vk
    wph
    @53
    vk
    fprodexp.kph
    @53
    vk
    nfv
    nfan
    vk
    @33
    cc
    vk
    @13
    cB
    nfcsb1v
    #
    nfel1
    nfim
    @46
    @13
    wceq
    #
    @55
    @56
    @48
    @38
    @58
    @50
    @53
    wph
    @46
    @13
    cA
    eleq1
    anbi2d
    @58
    cB
    @33
    cc
    vk
    @13
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    fprodexp.b
    chvar
    syl2anc
    #
    wph
    @39
    @30
    fprodexp.n
    adantr
    #
    @10
    @33
    cN
    mulexp
    syl3anc
    eqcomd
    adantr
    @32
    @15
    @9
    @34
    cmul
    co
    #
    @35
    @31
    @15
    @62
    wceq
    @12
    @31
    @8
    @13
    @1
    @34
    vk
    @28
    @40
    vk
    @33
    cN
    cexp
    @57
    vk
    cexp
    nfcv
    vk
    cN
    nfcv
    nfov
    @45
    @54
    @31
    @13
    cA
    @8
    @54
    eldifbd
    #
    wph
    @27
    @47
    @1
    cc
    wcel
    @29
    @49
    cB
    cN
    @51
    wph
    @39
    @27
    @47
    fprodexp.n
    ad2antrr
    expcld
    adantlrr
    @58
    cB
    @33
    cN
    cexp
    @59
    oveq1d
    @31
    @33
    cN
    @60
    @61
    expcld
    fprodsplitsn
    adantr
    @12
    @62
    @35
    wceq
    @31
    @9
    @11
    @34
    cmul
    oveq1
    adantl
    eqtrd
    @32
    @16
    @36
    cN
    cexp
    @31
    @16
    @36
    wceq
    @12
    @31
    @8
    @13
    cB
    @33
    vk
    @28
    @40
    @57
    @45
    @54
    @63
    @52
    @59
    @60
    fprodsplitsn
    adantr
    oveq1d
    3eqtr4d
    ex
    fprodexp.a
    findcard2d
end
