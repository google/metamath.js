include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "cmul.mm"
include "caddc.mm"
include "simp1l.mm"
include "simp3.mm"
include "expcl.mm"
include "syl2anc.mm"
include "simp2r.mm"
include "nnnn0d.mm"
include "cz.mm"
include "simp1r.mm"
include "nnzd.mm"
include "expne0i.mm"
include "syl3anc.mm"
include "divrec2d.mm"
include "wceq.mm"
include "simp2l.mm"
include "recnd.mm"
include "negnegd.mm"
include "nnnegz.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "nn0zd.mm"
include "zaddcld.mm"
include "expclz.mm"
include "adantr.mm"
include "divcan4d.mm"
include "simpr.mm"
include "expadd.mm"
include "cmin.mm"
include "zcnd.mm"
include "negsubd.mm"
include "nn0cnd.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "expneg2.mm"
include "znegcld.mm"
include "negdi2d.mm"
include "negcld.mm"
include "npcand.mm"
include "recdivd.mm"
include "wo.mm"
include "elznn0.mm"
include "simprbi.mm"
include "mpjaodan.mm"
include "3eqtr4d.mm"

theorem expaddzlem
  let cA: class A
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( M e. RR /\ -u M e. NN ) /\ N e. NN0 ) -> ( A ^ ( M + N ) ) = ( ( A ^ M ) x. ( A ^ N ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cM
    cr
    wcel
    #
    cM
    cneg
    #
    cn
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cN
    cexp
    co
    #
    cA
    @4
    cexp
    co
    #
    cdiv
    co
    #
    c1
    @10
    cdiv
    co
    #
    @9
    cmul
    co
    cA
    cM
    cN
    caddc
    co
    #
    cexp
    co
    #
    cA
    cM
    cexp
    co
    #
    @9
    cmul
    co
    @8
    @9
    @10
    @8
    @0
    @7
    @9
    cc
    wcel
    #
    @0
    @1
    @6
    @7
    simp1l
    #
    @2
    @6
    @7
    simp3
    #
    cA
    cN
    expcl
    syl2anc
    #
    @8
    @0
    @4
    cn0
    wcel
    #
    @10
    cc
    wcel
    #
    @17
    @8
    @4
    @2
    @3
    @5
    @7
    simp2r
    #
    nnnn0d
    #
    cA
    @4
    expcl
    syl2anc
    #
    @8
    @0
    @1
    @4
    cz
    wcel
    @10
    cc0
    wne
    #
    @17
    @0
    @1
    @6
    @7
    simp1r
    #
    @8
    @4
    @22
    nnzd
    cA
    @4
    expne0i
    syl3anc
    #
    divrec2d
    @8
    @13
    cn0
    wcel
    #
    @14
    @11
    wceq
    @13
    cneg
    #
    cn0
    wcel
    #
    @8
    @28
    wa
    #
    @14
    @10
    cmul
    co
    #
    @10
    cdiv
    co
    @14
    @11
    @31
    @14
    @10
    @8
    @14
    cc
    wcel
    #
    @28
    @8
    @0
    @1
    @13
    cz
    wcel
    #
    @33
    @17
    @26
    @8
    cM
    cN
    @8
    @4
    cneg
    #
    cM
    cz
    @8
    cM
    @8
    cM
    @2
    @3
    @5
    @7
    simp2l
    recnd
    #
    negnegd
    @8
    @5
    @35
    cz
    wcel
    @22
    @4
    nnnegz
    syl
    eqeltrrd
    @8
    cN
    @18
    nn0zd
    #
    zaddcld
    #
    cA
    @13
    expclz
    syl3anc
    adantr
    @8
    @21
    @28
    @24
    adantr
    @8
    @25
    @28
    @27
    adantr
    divcan4d
    @31
    @32
    @9
    @10
    cdiv
    @31
    cA
    @13
    @4
    caddc
    co
    #
    cexp
    co
    #
    @32
    @9
    @31
    @0
    @28
    @20
    @40
    @32
    wceq
    @8
    @0
    @28
    @17
    adantr
    @8
    @28
    simpr
    @8
    @20
    @28
    @23
    adantr
    cA
    @13
    @4
    expadd
    syl3anc
    @31
    @39
    cN
    cA
    cexp
    @8
    @39
    cN
    wceq
    @28
    @8
    @39
    @13
    cM
    cmin
    co
    cN
    @8
    @13
    cM
    @8
    @13
    @38
    zcnd
    #
    @36
    negsubd
    @8
    cM
    cN
    @36
    @8
    cN
    @18
    nn0cnd
    #
    pncan2d
    eqtrd
    adantr
    oveq2d
    eqtr3d
    oveq1d
    eqtr3d
    @8
    @30
    wa
    #
    @14
    c1
    cA
    @29
    cexp
    co
    #
    cdiv
    co
    #
    @11
    @43
    @0
    @13
    cc
    wcel
    #
    @30
    @14
    @45
    wceq
    @8
    @0
    @30
    @17
    adantr
    #
    @8
    @46
    @30
    @41
    adantr
    @8
    @30
    simpr
    #
    cA
    @13
    expneg2
    syl3anc
    @43
    @45
    c1
    @10
    @9
    cdiv
    co
    #
    cdiv
    co
    #
    @11
    @43
    @44
    @49
    c1
    cdiv
    @43
    @44
    @9
    cmul
    co
    #
    @9
    cdiv
    co
    @44
    @49
    @43
    @44
    @9
    @8
    @44
    cc
    wcel
    #
    @30
    @8
    @0
    @1
    @29
    cz
    wcel
    @52
    @17
    @26
    @8
    @13
    @38
    znegcld
    cA
    @29
    expclz
    syl3anc
    adantr
    @8
    @16
    @30
    @19
    adantr
    @8
    @9
    cc0
    wne
    #
    @30
    @8
    @0
    @1
    cN
    cz
    wcel
    @53
    @17
    @26
    @37
    cA
    cN
    expne0i
    syl3anc
    #
    adantr
    divcan4d
    @43
    @51
    @10
    @9
    cdiv
    @43
    cA
    @29
    cN
    caddc
    co
    #
    cexp
    co
    #
    @51
    @10
    @43
    @0
    @30
    @7
    @56
    @51
    wceq
    @47
    @48
    @8
    @7
    @30
    @18
    adantr
    cA
    @29
    cN
    expadd
    syl3anc
    @43
    @55
    @4
    cA
    cexp
    @8
    @55
    @4
    wceq
    @30
    @8
    @55
    @4
    cN
    cmin
    co
    #
    cN
    caddc
    co
    @4
    @8
    @29
    @57
    cN
    caddc
    @8
    cM
    cN
    @36
    @42
    negdi2d
    oveq1d
    @8
    @4
    cN
    @8
    cM
    @36
    negcld
    @42
    npcand
    eqtrd
    adantr
    oveq2d
    eqtr3d
    oveq1d
    eqtr3d
    oveq2d
    @8
    @50
    @11
    wceq
    @30
    @8
    @10
    @9
    @24
    @19
    @27
    @54
    recdivd
    adantr
    eqtrd
    eqtrd
    @8
    @34
    @28
    @30
    wo
    #
    @38
    @34
    @13
    cr
    wcel
    @58
    @13
    elznn0
    simprbi
    syl
    mpjaodan
    @8
    @15
    @12
    @9
    cmul
    @8
    @0
    cM
    cc
    wcel
    @20
    @15
    @12
    wceq
    @17
    @36
    @23
    cA
    cM
    expneg2
    syl3anc
    oveq1d
    3eqtr4d
end
