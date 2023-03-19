include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wo.mm"
include "elznn0nn.mm"
include "simpl.mm"
include "anim12i.mm"
include "mulexp.mm"
include "3expa.mm"
include "sylan.mm"
include "c1.mm"
include "cdiv.mm"
include "simplll.mm"
include "simplrl.mm"
include "mulcld.mm"
include "recn.mm"
include "ad2antrl.mm"
include "nnnn0.mm"
include "ad2antll.mm"
include "expneg2.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "1t1e1.mm"
include "oveq1i.mm"
include "syl6eqr.mm"
include "expcl.mm"
include "syl2anc.mm"
include "simpllr.mm"
include "nnz.mm"
include "expne0i.mm"
include "simplrr.mm"
include "ax-1cn.mm"
include "divmuldiv.mm"
include "mpanl12.mm"
include "syl22anc.mm"
include "eqtr4d.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "3impa.mm"

theorem mulexpz
  let cA: class A
  let cB: class B
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cM: class M


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) /\ N e. ZZ ) -> ( ( A x. B ) ^ N ) = ( ( A ^ N ) x. ( B ^ N ) ) )

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
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cN
    cz
    wcel
    #
    cA
    cB
    cmul
    co
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cB
    cN
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    @6
    @2
    @5
    wa
    #
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
    @12
    cN
    elznn0nn
    @13
    @14
    @12
    @18
    @13
    @0
    @3
    wa
    @14
    @12
    @2
    @0
    @5
    @3
    @0
    @1
    simpl
    @3
    @4
    simpl
    anim12i
    @0
    @3
    @14
    @12
    cA
    cB
    cN
    mulexp
    3expa
    sylan
    @13
    @18
    wa
    #
    @8
    c1
    @7
    @16
    cexp
    co
    #
    cdiv
    co
    #
    @11
    @19
    @7
    cc
    wcel
    cN
    cc
    wcel
    #
    @16
    cn0
    wcel
    #
    @8
    @21
    wceq
    @19
    cA
    cB
    @0
    @1
    @5
    @18
    simplll
    #
    @2
    @3
    @4
    @18
    simplrl
    #
    mulcld
    @15
    @22
    @13
    @17
    cN
    recn
    ad2antrl
    #
    @17
    @23
    @13
    @15
    @16
    nnnn0
    ad2antll
    #
    @7
    cN
    expneg2
    syl3anc
    @19
    @11
    c1
    cA
    @16
    cexp
    co
    #
    cdiv
    co
    #
    c1
    cB
    @16
    cexp
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @21
    @19
    @9
    @29
    @10
    @31
    cmul
    @19
    @0
    @22
    @23
    @9
    @29
    wceq
    @24
    @26
    @27
    cA
    cN
    expneg2
    syl3anc
    @19
    @3
    @22
    @23
    @10
    @31
    wceq
    @25
    @26
    @27
    cB
    cN
    expneg2
    syl3anc
    oveq12d
    @19
    @21
    c1
    c1
    cmul
    co
    #
    @28
    @30
    cmul
    co
    #
    cdiv
    co
    #
    @32
    @19
    @21
    c1
    @34
    cdiv
    co
    @35
    @19
    @20
    @34
    c1
    cdiv
    @19
    @0
    @3
    @23
    @20
    @34
    wceq
    @24
    @25
    @27
    cA
    cB
    @16
    mulexp
    syl3anc
    oveq2d
    @33
    c1
    @34
    cdiv
    1t1e1
    oveq1i
    syl6eqr
    @19
    @28
    cc
    wcel
    #
    @28
    cc0
    wne
    #
    @30
    cc
    wcel
    #
    @30
    cc0
    wne
    #
    @32
    @35
    wceq
    #
    @19
    @0
    @23
    @36
    @24
    @27
    cA
    @16
    expcl
    syl2anc
    @19
    @0
    @1
    @16
    cz
    wcel
    #
    @37
    @24
    @0
    @1
    @5
    @18
    simpllr
    @17
    @41
    @13
    @15
    @16
    nnz
    ad2antll
    #
    cA
    @16
    expne0i
    syl3anc
    @19
    @3
    @23
    @38
    @25
    @27
    cB
    @16
    expcl
    syl2anc
    @19
    @3
    @4
    @41
    @39
    @25
    @2
    @3
    @4
    @18
    simplrr
    @42
    cB
    @16
    expne0i
    syl3anc
    c1
    cc
    wcel
    #
    @43
    @36
    @37
    wa
    @38
    @39
    wa
    wa
    @40
    ax-1cn
    ax-1cn
    c1
    c1
    @28
    @30
    divmuldiv
    mpanl12
    syl22anc
    eqtr4d
    eqtr4d
    eqtr4d
    jaodan
    sylan2b
    3impa
end
