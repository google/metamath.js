include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "cc.mm"
include "recn.mm"
include "exp0.mm"
include "adantr.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "syl2an.mm"
include "cmul.mm"
include "simpll.mm"
include "reexpcl.mm"
include "sylan.mm"
include "simplll.mm"
include "simpr.mm"
include "simplrl.mm"
include "expge0.mm"
include "syl3anc.mm"
include "simplr.mm"
include "jca31.mm"
include "simpl.mm"
include "anim12i.mm"
include "simpllr.mm"
include "jca32.mm"
include "simplrr.mm"
include "jca.mm"
include "lemul12a.mm"
include "sylc.mm"
include "expp1.mm"
include "adantlr.mm"
include "adantll.mm"
include "3brtr4d.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "exp4c.mm"
include "com3l.mm"
include "3imp1.mm"

theorem leexp1a
  let cA: class A
  let cB: class B
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cM: class M


  assert |- ( ( ( A e. RR /\ B e. RR /\ N e. NN0 ) /\ ( 0 <_ A /\ A <_ B ) ) -> ( A ^ N ) <_ ( B ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    wa
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
    cle
    wbr
    #
    @2
    @0
    @1
    @5
    @8
    wi
    @2
    @0
    @1
    @5
    @8
    @0
    @1
    wa
    #
    @5
    wa
    #
    cA
    vj
    cv
    #
    cexp
    co
    #
    cB
    @11
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @10
    cA
    cc0
    cexp
    co
    #
    cB
    cc0
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @10
    cA
    vk
    cv
    #
    cexp
    co
    #
    cB
    @18
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @10
    cA
    @18
    c1
    caddc
    co
    #
    cexp
    co
    #
    cB
    @22
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @10
    @8
    wi
    vj
    vk
    cN
    @11
    cc0
    wceq
    #
    @14
    @17
    @10
    @26
    @12
    @15
    @13
    @16
    cle
    @11
    cc0
    cA
    cexp
    oveq2
    @11
    cc0
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @11
    @18
    wceq
    #
    @14
    @21
    @10
    @27
    @12
    @19
    @13
    @20
    cle
    @11
    @18
    cA
    cexp
    oveq2
    @11
    @18
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @11
    @22
    wceq
    #
    @14
    @25
    @10
    @28
    @12
    @23
    @13
    @24
    cle
    @11
    @22
    cA
    cexp
    oveq2
    @11
    @22
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @11
    cN
    wceq
    #
    @14
    @8
    @10
    @29
    @12
    @6
    @13
    @7
    cle
    @11
    cN
    cA
    cexp
    oveq2
    @11
    cN
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @9
    @17
    @5
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @17
    @1
    cA
    recn
    #
    cB
    recn
    #
    @30
    @31
    wa
    #
    @15
    c1
    @16
    cle
    @34
    @15
    c1
    c1
    cle
    @30
    @15
    c1
    wceq
    @31
    cA
    exp0
    adantr
    1le1
    syl6eqbr
    @31
    @16
    c1
    wceq
    @30
    cB
    exp0
    adantl
    breqtrrd
    syl2an
    adantr
    @18
    cn0
    wcel
    #
    @10
    @21
    @25
    @10
    @35
    @21
    @25
    wi
    @10
    @35
    wa
    #
    @21
    @25
    @36
    @21
    wa
    #
    @19
    cA
    cmul
    co
    #
    @20
    cB
    cmul
    co
    #
    @23
    @24
    cle
    @37
    @19
    cr
    wcel
    #
    cc0
    @19
    cle
    wbr
    #
    wa
    @20
    cr
    wcel
    #
    wa
    #
    @0
    @3
    wa
    #
    @1
    wa
    wa
    #
    @21
    @4
    wa
    @38
    @39
    cle
    wbr
    @36
    @45
    @21
    @36
    @43
    @44
    @1
    @36
    @40
    @41
    @42
    @10
    @0
    @35
    @40
    @0
    @1
    @5
    simpll
    cA
    @18
    reexpcl
    sylan
    @36
    @0
    @35
    @3
    @41
    @0
    @1
    @5
    @35
    simplll
    @10
    @35
    simpr
    @9
    @3
    @4
    @35
    simplrl
    cA
    @18
    expge0
    syl3anc
    @10
    @1
    @35
    @42
    @0
    @1
    @5
    simplr
    cB
    @18
    reexpcl
    sylan
    jca31
    @10
    @44
    @35
    @9
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
    adantr
    @0
    @1
    @5
    @35
    simpllr
    jca32
    adantr
    @37
    @21
    @4
    @36
    @21
    simpr
    @36
    @4
    @21
    @9
    @3
    @4
    @35
    simplrr
    adantr
    jca
    @19
    @20
    cA
    cB
    lemul12a
    sylc
    @36
    @23
    @38
    wceq
    #
    @21
    @9
    @35
    @46
    @5
    @0
    @35
    @46
    @1
    @0
    @30
    @35
    @46
    @32
    cA
    @18
    expp1
    sylan
    adantlr
    adantlr
    adantr
    @36
    @24
    @39
    wceq
    #
    @21
    @9
    @35
    @47
    @5
    @1
    @35
    @47
    @0
    @1
    @31
    @35
    @47
    @33
    cB
    @18
    expp1
    sylan
    adantll
    adantlr
    adantr
    3brtr4d
    ex
    expcom
    a2d
    nn0ind
    exp4c
    com3l
    3imp1
end
