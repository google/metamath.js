include "cn0.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "ccxp.mm"
include "cv.mm"
include "cbcc.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "binomcxplemnn0.mm"
include "cabs.mm"
include "ccnv.mm"
include "cc0.mm"
include "cc.mm"
include "cmpt.mm"
include "cfv.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cr.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cico.mm"
include "cima.mm"
include "cn.mm"
include "c1.mm"
include "eqid.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "id.mm"
include "a1i.mm"
include "fveq12d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq1i.mm"
include "oveq1i.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "eleq1i.mm"
include "rabbii.mm"
include "supeq1i.mm"
include "oveq2i.mm"
include "imaeq2i.mm"
include "binomcxplemnotnn0.mm"
include "pm2.61dan.mm"

theorem binomcxp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vb: setvar b
  let vj: setvar j
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )

  disjoint C k
  disjoint k ph
  disjoint A k
  disjoint B k
  disjoint b j
  disjoint b k
  disjoint b r
  disjoint b x
  disjoint C b
  disjoint j k
  disjoint j r
  disjoint j x
  disjoint C j
  disjoint k r
  disjoint k x
  disjoint r x
  disjoint C r
  disjoint C x
  disjoint b ph
  disjoint j ph
  disjoint A b
  disjoint A r
  disjoint B b
  disjoint B r
  disjoint j y
  disjoint k y
  disjoint C y
  assert |- ( ph -> ( ( A + B ) ^c C ) = sum_ k e. NN0 ( ( C _Cc k ) x. ( ( A ^c ( C - k ) ) x. ( B ^ k ) ) ) )

  proof
    wph
    cC
    cn0
    wcel
    cA
    cB
    caddc
    co
    cC
    ccxp
    co
    cn0
    cC
    vk
    cv
    #
    cbcc
    co
    cA
    cC
    @0
    cmin
    co
    ccxp
    co
    cB
    @0
    cexp
    co
    cmul
    co
    cmul
    co
    vk
    csu
    wceq
    wph
    cA
    cB
    cC
    vk
    binomcxp.a
    binomcxp.b
    binomcxp.lt
    binomcxp.c
    binomcxplemnn0
    wph
    cA
    cB
    cC
    cabs
    ccnv
    #
    cc0
    caddc
    vr
    cv
    #
    vb
    cc
    vx
    cn0
    vx
    cv
    #
    vx
    cn0
    cC
    @3
    cbcc
    co
    #
    cmpt
    #
    cfv
    #
    vb
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    cico
    co
    #
    cima
    #
    vb
    @19
    cn0
    @0
    @7
    vb
    cc
    vx
    cn0
    @3
    vj
    cn0
    cC
    vj
    cv
    #
    cbcc
    co
    #
    cmpt
    #
    cfv
    #
    @8
    cmul
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    cfv
    vk
    csu
    cmpt
    #
    caddc
    @2
    @26
    cfv
    #
    cc0
    cseq
    #
    @14
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    @26
    vj
    vk
    vb
    cc
    vx
    cn
    @3
    @3
    vy
    cn0
    cC
    vy
    cv
    #
    cbcc
    co
    #
    cmpt
    #
    cfv
    #
    cmul
    co
    #
    @7
    @3
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    @22
    vr
    vb
    binomcxp.a
    binomcxp.b
    binomcxp.lt
    binomcxp.c
    @22
    eqid
    vb
    cc
    @25
    vk
    cn0
    @0
    @22
    cfv
    #
    @7
    @0
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    vx
    vk
    cn0
    @24
    @44
    @3
    @0
    wceq
    #
    @23
    @42
    @8
    @43
    cmul
    @3
    @0
    @22
    fveq2
    @3
    @0
    @7
    cexp
    oveq2
    oveq12d
    cbvmptv
    mpteq2i
    @32
    eqid
    vb
    cc
    @41
    vk
    cn
    @0
    @42
    cmul
    co
    #
    @7
    @0
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    vx
    vk
    cn
    @40
    @49
    @45
    @37
    @46
    @39
    @48
    cmul
    @45
    @3
    @0
    @36
    @42
    cmul
    @45
    id
    #
    @45
    @3
    @0
    @35
    @22
    @35
    @22
    wceq
    @45
    vy
    vj
    cn0
    @34
    @21
    @33
    @20
    cC
    cbcc
    oveq2
    cbvmptv
    a1i
    @50
    fveq12d
    oveq12d
    @45
    @38
    @47
    @7
    cexp
    @3
    @0
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    cbvmptv
    mpteq2i
    @18
    cc0
    @32
    cico
    co
    @1
    @17
    @32
    cc0
    cico
    cxr
    @16
    @31
    clt
    @15
    @30
    vr
    cr
    @13
    @29
    @14
    @12
    @28
    wceq
    @13
    @29
    wceq
    @2
    @11
    @26
    vb
    cc
    @10
    @25
    vx
    cn0
    @9
    @24
    @6
    @23
    @8
    cmul
    @3
    @5
    @22
    vx
    vj
    cn0
    @4
    @21
    @3
    @20
    cC
    cbcc
    oveq2
    cbvmptv
    fveq1i
    oveq1i
    mpteq2i
    mpteq2i
    fveq1i
    caddc
    @12
    @28
    cc0
    seqeq3
    ax-mp
    eleq1i
    rabbii
    supeq1i
    oveq2i
    imaeq2i
    @27
    eqid
    binomcxplemnotnn0
    pm2.61dan
end
