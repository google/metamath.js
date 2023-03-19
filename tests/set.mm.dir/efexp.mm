include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cexp.mm"
include "wceq.mm"
include "zcn.mm"
include "mulcom.mm"
include "sylan2.mm"
include "fveq2d.mm"
include "cv.mm"
include "cc0.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ef0.mm"
include "mul01.mm"
include "efcl.mm"
include "exp0d.mm"
include "3eqtr4a.mm"
include "cn0.mm"
include "oveq1.mm"
include "adantl.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an3.mm"
include "mulid1.mm"
include "adantr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mulcl.mm"
include "simpl.mm"
include "efadd.mm"
include "syl2anc.mm"
include "expp1.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "exp31.mm"
include "cn.mm"
include "wi.mm"
include "cdiv.mm"
include "nncn.mm"
include "mulneg2.mm"
include "efneg.mm"
include "syl.mm"
include "nnnn0.mm"
include "expneg.mm"
include "syl2an.mm"
include "syl5ibr.mm"
include "ex.mm"
include "zindd.mm"
include "imp.mm"
include "eqtr3d.mm"

theorem efexp
  let cA: class A
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. ZZ ) -> ( exp ` ( N x. A ) ) = ( ( exp ` A ) ^ N ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    cmul
    co
    #
    ce
    cfv
    #
    cN
    cA
    cmul
    co
    #
    ce
    cfv
    cA
    ce
    cfv
    #
    cN
    cexp
    co
    #
    @2
    @3
    @5
    ce
    @1
    @0
    cN
    cc
    wcel
    @3
    @5
    wceq
    cN
    zcn
    cA
    cN
    mulcom
    sylan2
    fveq2d
    @0
    @1
    @4
    @7
    wceq
    #
    cA
    vj
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @6
    @9
    cexp
    co
    #
    wceq
    cA
    cc0
    cmul
    co
    #
    ce
    cfv
    #
    @6
    cc0
    cexp
    co
    #
    wceq
    cA
    vk
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @6
    @16
    cexp
    co
    #
    wceq
    #
    cA
    @16
    cneg
    #
    cmul
    co
    #
    ce
    cfv
    #
    @6
    @21
    cexp
    co
    #
    wceq
    #
    cA
    @16
    c1
    caddc
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    @6
    @26
    cexp
    co
    #
    wceq
    #
    @8
    @0
    vj
    vk
    cN
    @9
    cc0
    wceq
    #
    @11
    @14
    @12
    @15
    @31
    @10
    @13
    ce
    @9
    cc0
    cA
    cmul
    oveq2
    fveq2d
    @9
    cc0
    @6
    cexp
    oveq2
    eqeq12d
    @9
    @16
    wceq
    #
    @11
    @18
    @12
    @19
    @32
    @10
    @17
    ce
    @9
    @16
    cA
    cmul
    oveq2
    fveq2d
    @9
    @16
    @6
    cexp
    oveq2
    eqeq12d
    @9
    @26
    wceq
    #
    @11
    @28
    @12
    @29
    @33
    @10
    @27
    ce
    @9
    @26
    cA
    cmul
    oveq2
    fveq2d
    @9
    @26
    @6
    cexp
    oveq2
    eqeq12d
    @9
    @21
    wceq
    #
    @11
    @23
    @12
    @24
    @34
    @10
    @22
    ce
    @9
    @21
    cA
    cmul
    oveq2
    fveq2d
    @9
    @21
    @6
    cexp
    oveq2
    eqeq12d
    @9
    cN
    wceq
    #
    @11
    @4
    @12
    @7
    @35
    @10
    @3
    ce
    @9
    cN
    cA
    cmul
    oveq2
    fveq2d
    @9
    cN
    @6
    cexp
    oveq2
    eqeq12d
    @0
    cc0
    ce
    cfv
    c1
    @14
    @15
    ef0
    @0
    @13
    cc0
    ce
    cA
    mul01
    fveq2d
    @0
    @6
    cA
    efcl
    #
    exp0d
    3eqtr4a
    @0
    @16
    cn0
    wcel
    #
    @20
    @30
    @0
    @37
    wa
    #
    @20
    wa
    @18
    @6
    cmul
    co
    #
    @19
    @6
    cmul
    co
    #
    @28
    @29
    @20
    @39
    @40
    wceq
    @38
    @18
    @19
    @6
    cmul
    oveq1
    adantl
    @38
    @28
    @39
    wceq
    @20
    @38
    @28
    @17
    cA
    caddc
    co
    #
    ce
    cfv
    #
    @39
    @38
    @27
    @41
    ce
    @37
    @0
    @16
    cc
    wcel
    #
    @27
    @41
    wceq
    @16
    nn0cn
    #
    @0
    @43
    wa
    #
    @27
    @17
    cA
    c1
    cmul
    co
    #
    caddc
    co
    #
    @41
    @0
    @43
    c1
    cc
    wcel
    @27
    @47
    wceq
    ax-1cn
    cA
    @16
    c1
    adddi
    mp3an3
    @45
    @46
    cA
    @17
    caddc
    @0
    @46
    cA
    wceq
    @43
    cA
    mulid1
    adantr
    oveq2d
    eqtrd
    sylan2
    fveq2d
    @38
    @17
    cc
    wcel
    #
    @0
    @42
    @39
    wceq
    @37
    @0
    @43
    @48
    @44
    cA
    @16
    mulcl
    #
    sylan2
    @0
    @37
    simpl
    @17
    cA
    efadd
    syl2anc
    eqtrd
    adantr
    @38
    @29
    @40
    wceq
    #
    @20
    @0
    @6
    cc
    wcel
    #
    @37
    @50
    @36
    @6
    @16
    expp1
    sylan
    adantr
    3eqtr4d
    exp31
    @0
    @16
    cn
    wcel
    #
    @20
    @25
    wi
    @20
    @25
    @0
    @52
    wa
    #
    c1
    @18
    cdiv
    co
    #
    c1
    @19
    cdiv
    co
    #
    wceq
    @18
    @19
    c1
    cdiv
    oveq2
    @53
    @23
    @54
    @24
    @55
    @53
    @23
    @17
    cneg
    #
    ce
    cfv
    #
    @54
    @53
    @22
    @56
    ce
    @52
    @0
    @43
    @22
    @56
    wceq
    @16
    nncn
    #
    cA
    @16
    mulneg2
    sylan2
    fveq2d
    @53
    @48
    @57
    @54
    wceq
    @52
    @0
    @43
    @48
    @58
    @49
    sylan2
    @17
    efneg
    syl
    eqtrd
    @0
    @51
    @37
    @24
    @55
    wceq
    @52
    @36
    @16
    nnnn0
    @6
    @16
    expneg
    syl2an
    eqeq12d
    syl5ibr
    ex
    zindd
    imp
    eqtr3d
end
