include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "cz.mm"
include "reexpcl.mm"
include "adantr.mm"
include "leidd.mm"
include "a1i.mm"
include "cmul.mm"
include "simprll.mm"
include "1red.mm"
include "simprlr.mm"
include "simpl.mm"
include "eluznn0.mm"
include "syl2anc.mm"
include "simprrl.mm"
include "expge0.mm"
include "syl3anc.mm"
include "simprrr.mm"
include "lemul2ad.mm"
include "cc.mm"
include "recnd.mm"
include "expp1.mm"
include "mulid1d.mm"
include "eqcomd.mm"
include "3brtr4d.mm"
include "peano2nn0.mm"
include "syl.mm"
include "ad2antrl.mm"
include "letr.mm"
include "mpand.mm"
include "ex.mm"
include "a2d.mm"
include "uzind4.mm"
include "expd.mm"
include "com12.mm"
include "3impia.mm"
include "imp.mm"

theorem leexp2r
  let cA: class A
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cB: class B


  assert |- ( ( ( A e. RR /\ M e. NN0 /\ N e. ( ZZ>= ` M ) ) /\ ( 0 <_ A /\ A <_ 1 ) ) -> ( A ^ N ) <_ ( A ^ M ) )

  proof
    cA
    cr
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    w3a
    cc0
    cA
    cle
    wbr
    #
    cA
    c1
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
    cA
    cM
    cexp
    co
    #
    cle
    wbr
    #
    @0
    @1
    @3
    @6
    @9
    wi
    #
    @3
    @0
    @1
    wa
    #
    @10
    @3
    @11
    @6
    @9
    @11
    @6
    wa
    #
    cA
    vj
    cv
    #
    cexp
    co
    #
    @8
    cle
    wbr
    #
    wi
    @12
    @8
    @8
    cle
    wbr
    #
    wi
    #
    @12
    cA
    vk
    cv
    #
    cexp
    co
    #
    @8
    cle
    wbr
    #
    wi
    @12
    cA
    @18
    c1
    caddc
    co
    #
    cexp
    co
    #
    @8
    cle
    wbr
    #
    wi
    @12
    @9
    wi
    vj
    vk
    cM
    cN
    @13
    cM
    wceq
    #
    @15
    @16
    @12
    @24
    @14
    @8
    @8
    cle
    @13
    cM
    cA
    cexp
    oveq2
    breq1d
    imbi2d
    @13
    @18
    wceq
    #
    @15
    @20
    @12
    @25
    @14
    @19
    @8
    cle
    @13
    @18
    cA
    cexp
    oveq2
    breq1d
    imbi2d
    @13
    @21
    wceq
    #
    @15
    @23
    @12
    @26
    @14
    @22
    @8
    cle
    @13
    @21
    cA
    cexp
    oveq2
    breq1d
    imbi2d
    @13
    cN
    wceq
    #
    @15
    @9
    @12
    @27
    @14
    @7
    @8
    cle
    @13
    cN
    cA
    cexp
    oveq2
    breq1d
    imbi2d
    @17
    cM
    cz
    wcel
    @12
    @8
    @11
    @8
    cr
    wcel
    #
    @6
    cA
    cM
    reexpcl
    #
    adantr
    leidd
    a1i
    @18
    @2
    wcel
    #
    @12
    @20
    @23
    @30
    @12
    @20
    @23
    wi
    @30
    @12
    wa
    #
    @22
    @19
    cle
    wbr
    #
    @20
    @23
    @31
    @19
    cA
    cmul
    co
    #
    @19
    c1
    cmul
    co
    #
    @22
    @19
    cle
    @31
    cA
    c1
    @19
    @30
    @0
    @1
    @6
    simprll
    #
    @31
    1red
    @31
    @0
    @18
    cn0
    wcel
    #
    @19
    cr
    wcel
    #
    @35
    @31
    @1
    @30
    @36
    @30
    @0
    @1
    @6
    simprlr
    @30
    @12
    simpl
    @18
    cM
    eluznn0
    syl2anc
    #
    cA
    @18
    reexpcl
    syl2anc
    #
    @31
    @0
    @36
    @4
    cc0
    @19
    cle
    wbr
    @35
    @38
    @30
    @11
    @4
    @5
    simprrl
    cA
    @18
    expge0
    syl3anc
    @30
    @11
    @4
    @5
    simprrr
    lemul2ad
    @31
    cA
    cc
    wcel
    @36
    @22
    @33
    wceq
    @31
    cA
    @35
    recnd
    @38
    cA
    @18
    expp1
    syl2anc
    @31
    @34
    @19
    @31
    @19
    @31
    @19
    @39
    recnd
    mulid1d
    eqcomd
    3brtr4d
    @31
    @22
    cr
    wcel
    #
    @37
    @28
    @32
    @20
    wa
    @23
    wi
    @31
    @0
    @21
    cn0
    wcel
    #
    @40
    @35
    @31
    @36
    @41
    @38
    @18
    peano2nn0
    syl
    cA
    @21
    reexpcl
    syl2anc
    @39
    @11
    @28
    @30
    @6
    @29
    ad2antrl
    @22
    @19
    @8
    letr
    syl3anc
    mpand
    ex
    a2d
    uzind4
    expd
    com12
    3impia
    imp
end
