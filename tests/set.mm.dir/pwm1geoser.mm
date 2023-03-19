include "c1.mm"
include "wceq.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "wi.mm"
include "1m1e0.mm"
include "cz.mm"
include "wcel.mm"
include "nn0zd.mm"
include "1exp.mm"
include "syl.mm"
include "oveq1d.mm"
include "fzfid.mm"
include "wa.mm"
include "1cnd.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "expcld.mm"
include "fsumcl.mm"
include "mul02d.mm"
include "3eqtr4a.mm"
include "oveq1.mm"
include "syl6eq.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "sumeq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "wn.mm"
include "cdiv.mm"
include "cc.mm"
include "wne.mm"
include "neqne.mm"
include "geoser.mm"
include "eqcom.mm"
include "nesym.mm"
include "biimpri.mm"
include "div2subd.mm"
include "eqeq1d.mm"
include "wb.mm"
include "peano2cnm.mm"
include "simpl.mm"
include "subne0d.mm"
include "jca.mm"
include "ex.mm"
include "impcom.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "mpbid.mm"
include "pm2.61i.mm"

theorem pwm1geoser
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cN: class N
  assume pwm1geoser.1: |- ( ph -> A e. CC )
  assume pwm1geoser.3: |- ( ph -> N e. NN0 )

  disjoint A k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( ( A ^ N ) - 1 ) = ( ( A - 1 ) x. sum_ k e. ( 0 ... ( N - 1 ) ) ( A ^ k ) ) )

  proof
    cA
    c1
    wceq
    #
    wph
    cA
    cN
    cexp
    co
    #
    c1
    cmin
    co
    #
    cA
    c1
    cmin
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    wi
    wph
    @10
    @0
    c1
    cN
    cexp
    co
    #
    c1
    cmin
    co
    #
    cc0
    @5
    c1
    @6
    cexp
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    wceq
    wph
    c1
    c1
    cmin
    co
    #
    cc0
    @12
    @15
    1m1e0
    wph
    @11
    c1
    c1
    cmin
    wph
    cN
    cz
    wcel
    @11
    c1
    wceq
    wph
    cN
    pwm1geoser.3
    nn0zd
    cN
    1exp
    syl
    oveq1d
    wph
    @14
    wph
    @5
    @13
    vk
    wph
    cc0
    @4
    fzfid
    wph
    @6
    @5
    wcel
    #
    wa
    #
    c1
    @6
    @18
    1cnd
    @17
    @6
    cn0
    wcel
    #
    wph
    @6
    @4
    elfznn0
    #
    adantl
    expcld
    fsumcl
    mul02d
    3eqtr4a
    @0
    @2
    @12
    @9
    @15
    @0
    @1
    @11
    c1
    cmin
    cA
    c1
    cN
    cexp
    oveq1
    oveq1d
    @0
    @3
    cc0
    @8
    @14
    cmul
    @0
    @3
    @16
    cc0
    cA
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    @0
    @5
    @7
    @13
    vk
    @0
    @7
    @13
    wceq
    #
    vk
    @5
    @0
    @21
    @17
    cA
    c1
    @6
    cexp
    oveq1
    adantr
    ralrimiva
    sumeq2d
    oveq12d
    eqeq12d
    syl5ibr
    @0
    wn
    #
    wph
    @10
    @22
    wph
    wa
    #
    @8
    c1
    @1
    cmin
    co
    c1
    cA
    cmin
    co
    cdiv
    co
    #
    wceq
    #
    @10
    @23
    cA
    vk
    cN
    wph
    cA
    cc
    wcel
    #
    @22
    pwm1geoser.1
    adantl
    #
    @22
    cA
    c1
    wne
    #
    wph
    cA
    c1
    neqne
    #
    adantr
    wph
    cN
    cn0
    wcel
    @22
    pwm1geoser.3
    adantl
    geoser
    @25
    @24
    @8
    wceq
    #
    @23
    @10
    @8
    @24
    eqcom
    @23
    @30
    @2
    @3
    cdiv
    co
    #
    @8
    wceq
    #
    @10
    @23
    @24
    @31
    @8
    @23
    c1
    @1
    c1
    cA
    @23
    1cnd
    #
    wph
    @1
    cc
    wcel
    #
    @22
    wph
    cA
    cN
    pwm1geoser.1
    pwm1geoser.3
    expcld
    #
    adantl
    @33
    @27
    @22
    c1
    cA
    wne
    #
    wph
    @36
    @22
    c1
    cA
    nesym
    biimpri
    adantr
    div2subd
    eqeq1d
    @23
    @2
    cc
    wcel
    #
    @8
    cc
    wcel
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    wa
    #
    @32
    @10
    wb
    wph
    @37
    @22
    wph
    @34
    @37
    @35
    @1
    peano2cnm
    syl
    adantl
    @23
    @5
    @7
    vk
    @23
    cc0
    @4
    fzfid
    @23
    @17
    wa
    cA
    @6
    @23
    @26
    @17
    @27
    adantr
    @17
    @19
    @23
    @20
    adantl
    expcld
    fsumcl
    wph
    @22
    @40
    wph
    @26
    @22
    @40
    wi
    pwm1geoser.1
    @26
    @22
    @40
    @26
    @22
    wa
    #
    @38
    @39
    @26
    @38
    @22
    cA
    peano2cnm
    adantr
    @41
    cA
    c1
    @26
    @22
    simpl
    @41
    1cnd
    @22
    @28
    @26
    @29
    adantl
    subne0d
    jca
    ex
    syl
    impcom
    @2
    @8
    @3
    divmul2
    syl3anc
    bitrd
    syl5bb
    mpbid
    ex
    pm2.61i
end
