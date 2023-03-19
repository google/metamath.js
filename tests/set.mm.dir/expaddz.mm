include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wo.mm"
include "elznn0nn.mm"
include "wi.mm"
include "expadd.mm"
include "3expia.mm"
include "adantlr.mm"
include "expaddzlem.mm"
include "jaodan.mm"
include "w3a.mm"
include "simp3.mm"
include "nn0cnd.mm"
include "simp2l.mm"
include "recnd.mm"
include "addcomd.mm"
include "oveq2d.mm"
include "simp1l.mm"
include "expcl.mm"
include "syl2anc.mm"
include "simp1r.mm"
include "negnegd.mm"
include "simp2r.mm"
include "nnnn0d.mm"
include "nn0negz.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "expclz.mm"
include "syl3anc.mm"
include "mulcomd.mm"
include "3eqtr4d.mm"
include "impancom.mm"
include "c1.mm"
include "cdiv.mm"
include "simp3l.mm"
include "negdid.mm"
include "simp3r.mm"
include "eqtrd.mm"
include "1t1e1.mm"
include "oveq1i.mm"
include "syl6eqr.mm"
include "nn0zd.mm"
include "expne0i.mm"
include "ax-1cn.mm"
include "divmuldiv.mm"
include "mpanl12.mm"
include "syl22anc.mm"
include "eqtr4d.mm"
include "addcld.mm"
include "nn0addcld.mm"
include "eqeltrd.mm"
include "expneg2.mm"
include "oveq12d.mm"
include "jaod.mm"
include "sylan2b.mm"
include "syl5bi.mm"
include "impr.mm"

theorem expaddz
  let cA: class A
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( M e. ZZ /\ N e. ZZ ) ) -> ( A ^ ( M + N ) ) = ( ( A ^ M ) x. ( A ^ N ) ) )

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
    cz
    wcel
    #
    cN
    cz
    wcel
    #
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
    cA
    cN
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    @4
    cN
    cn0
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    #
    @2
    @3
    wa
    @10
    cN
    elznn0nn
    @3
    @2
    cM
    cn0
    wcel
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
    wo
    #
    @16
    @10
    wi
    cM
    elznn0nn
    @2
    @22
    wa
    @11
    @10
    @15
    @2
    @17
    @11
    @10
    wi
    #
    @21
    @0
    @17
    @23
    @1
    @0
    @17
    @11
    @10
    cA
    cM
    cN
    expadd
    3expia
    adantlr
    @2
    @21
    @11
    @10
    cA
    cM
    cN
    expaddzlem
    3expia
    jaodan
    @2
    @17
    @15
    @10
    wi
    @21
    @2
    @15
    @17
    @10
    @2
    @15
    @17
    @10
    @2
    @15
    @17
    w3a
    #
    cA
    cN
    cM
    caddc
    co
    #
    cexp
    co
    @8
    @7
    cmul
    co
    @6
    @9
    cA
    cN
    cM
    expaddzlem
    @24
    @5
    @25
    cA
    cexp
    @24
    cM
    cN
    @24
    cM
    @2
    @15
    @17
    simp3
    #
    nn0cnd
    @24
    cN
    @2
    @12
    @14
    @17
    simp2l
    recnd
    #
    addcomd
    oveq2d
    @24
    @7
    @8
    @24
    @0
    @17
    @7
    cc
    wcel
    @0
    @1
    @15
    @17
    simp1l
    #
    @26
    cA
    cM
    expcl
    syl2anc
    @24
    @0
    @1
    @4
    @8
    cc
    wcel
    @28
    @0
    @1
    @15
    @17
    simp1r
    @24
    @13
    cneg
    #
    cN
    cz
    @24
    cN
    @27
    negnegd
    @24
    @13
    cn0
    wcel
    #
    @29
    cz
    wcel
    @24
    @13
    @2
    @12
    @14
    @17
    simp2r
    nnnn0d
    @13
    nn0negz
    syl
    eqeltrrd
    cA
    cN
    expclz
    syl3anc
    mulcomd
    3eqtr4d
    3expia
    impancom
    @2
    @21
    @15
    @10
    @2
    @21
    @15
    w3a
    #
    c1
    cA
    @5
    cneg
    #
    cexp
    co
    #
    cdiv
    co
    #
    c1
    cA
    @19
    cexp
    co
    #
    cdiv
    co
    #
    c1
    cA
    @13
    cexp
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @6
    @9
    @31
    @34
    c1
    c1
    cmul
    co
    #
    @35
    @37
    cmul
    co
    #
    cdiv
    co
    #
    @39
    @31
    @34
    c1
    @41
    cdiv
    co
    @42
    @31
    @33
    @41
    c1
    cdiv
    @31
    @33
    cA
    @19
    @13
    caddc
    co
    #
    cexp
    co
    #
    @41
    @31
    @32
    @43
    cA
    cexp
    @31
    cM
    cN
    @31
    cM
    @2
    @18
    @20
    @15
    simp2l
    recnd
    #
    @31
    cN
    @2
    @21
    @12
    @14
    simp3l
    recnd
    #
    negdid
    #
    oveq2d
    @31
    @0
    @19
    cn0
    wcel
    #
    @30
    @44
    @41
    wceq
    @0
    @1
    @21
    @15
    simp1l
    #
    @31
    @19
    @2
    @18
    @20
    @15
    simp2r
    nnnn0d
    #
    @31
    @13
    @2
    @21
    @12
    @14
    simp3r
    nnnn0d
    #
    cA
    @19
    @13
    expadd
    syl3anc
    eqtrd
    oveq2d
    @40
    c1
    @41
    cdiv
    1t1e1
    oveq1i
    syl6eqr
    @31
    @35
    cc
    wcel
    #
    @35
    cc0
    wne
    #
    @37
    cc
    wcel
    #
    @37
    cc0
    wne
    #
    @39
    @42
    wceq
    #
    @31
    @0
    @48
    @52
    @49
    @50
    cA
    @19
    expcl
    syl2anc
    @31
    @0
    @1
    @19
    cz
    wcel
    @53
    @49
    @0
    @1
    @21
    @15
    simp1r
    #
    @31
    @19
    @50
    nn0zd
    cA
    @19
    expne0i
    syl3anc
    @31
    @0
    @30
    @54
    @49
    @51
    cA
    @13
    expcl
    syl2anc
    @31
    @0
    @1
    @13
    cz
    wcel
    @55
    @49
    @57
    @31
    @13
    @51
    nn0zd
    cA
    @13
    expne0i
    syl3anc
    c1
    cc
    wcel
    #
    @58
    @52
    @53
    wa
    @54
    @55
    wa
    wa
    @56
    ax-1cn
    ax-1cn
    c1
    c1
    @35
    @37
    divmuldiv
    mpanl12
    syl22anc
    eqtr4d
    @31
    @0
    @5
    cc
    wcel
    @32
    cn0
    wcel
    @6
    @34
    wceq
    @49
    @31
    cM
    cN
    @45
    @46
    addcld
    @31
    @32
    @43
    cn0
    @47
    @31
    @19
    @13
    @50
    @51
    nn0addcld
    eqeltrd
    cA
    @5
    expneg2
    syl3anc
    @31
    @7
    @36
    @8
    @38
    cmul
    @31
    @0
    cM
    cc
    wcel
    @48
    @7
    @36
    wceq
    @49
    @45
    @50
    cA
    cM
    expneg2
    syl3anc
    @31
    @0
    cN
    cc
    wcel
    @30
    @8
    @38
    wceq
    @49
    @46
    @51
    cA
    cN
    expneg2
    syl3anc
    oveq12d
    3eqtr4d
    3expia
    jaodan
    jaod
    sylan2b
    syl5bi
    impr
end
