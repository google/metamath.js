include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "co.mm"
include "zring.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "cv.mm"
include "cmpt.mm"
include "caddc.mm"
include "cbs.mm"
include "crg.mm"
include "cvv.mm"
include "eqid.mm"
include "zringring.mm"
include "a1i.mm"
include "prex.mm"
include "simpl.mm"
include "zlmodzxzel.mm"
include "syl2an.mm"
include "simpr.mm"
include "frlmplusgval.mm"
include "wne.mm"
include "wfn.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "anim12i.mm"
include "0ne1.mm"
include "fnprg.mm"
include "syl3anc.mm"
include "offvalfv.mm"
include "zringplusg.mm"
include "eqcomi.mm"
include "oveqi.mm"
include "opeq2i.mm"
include "preq12i.mm"
include "ovexd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "adantr.mm"
include "fvpr1g.mm"
include "sylan9eqr.mm"
include "adantl.mm"
include "fvpr2g.mm"
include "fmptpr.mm"
include "syl5reqr.mm"
include "3eqtrd.mm"

theorem zlmodzxzadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume zlmodzxz.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzadd.p: |- .+ = ( +g ` Z )


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) ) -> ( { <. 0 , A >. , <. 1 , C >. } .+ { <. 0 , B >. , <. 1 , D >. } ) = { <. 0 , ( A + B ) >. , <. 1 , ( C + D ) >. } )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    wa
    #
    cc0
    cA
    cop
    c1
    cC
    cop
    cpr
    #
    cc0
    cB
    cop
    c1
    cD
    cop
    cpr
    #
    c.pl
    co
    @7
    @8
    zring
    cplusg
    cfv
    #
    cof
    co
    vx
    cc0
    c1
    cpr
    #
    vx
    cv
    #
    @7
    cfv
    #
    @11
    @8
    cfv
    #
    @9
    co
    #
    cmpt
    #
    cc0
    cA
    cB
    caddc
    co
    #
    cop
    #
    c1
    cC
    cD
    caddc
    co
    #
    cop
    #
    cpr
    #
    @6
    cZ
    cbs
    cfv
    #
    @9
    c.pl
    zring
    @7
    @8
    @10
    crg
    cvv
    cZ
    zlmodzxz.z
    @21
    eqid
    zring
    crg
    wcel
    @6
    zringring
    a1i
    @10
    cvv
    wcel
    @6
    cc0
    c1
    prex
    a1i
    #
    @2
    @0
    @3
    @7
    @21
    wcel
    @5
    @0
    @1
    simpl
    #
    @3
    @4
    simpl
    #
    cA
    cC
    cZ
    zlmodzxz.z
    zlmodzxzel
    syl2an
    @2
    @1
    @4
    @8
    @21
    wcel
    @5
    @0
    @1
    simpr
    #
    @3
    @4
    simpr
    #
    cB
    cD
    cZ
    zlmodzxz.z
    zlmodzxzel
    syl2an
    @9
    eqid
    zlmodzxzadd.p
    frlmplusgval
    @6
    vx
    @10
    @9
    @7
    @8
    cvv
    @22
    @6
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    #
    @0
    @3
    wa
    cc0
    c1
    wne
    #
    @7
    @10
    wfn
    @29
    @6
    @27
    @28
    c0ex
    1ex
    pm3.2i
    a1i
    #
    @2
    @0
    @5
    @3
    @23
    @24
    anim12i
    @30
    @6
    0ne1
    a1i
    #
    cc0
    c1
    cA
    cC
    cvv
    cvv
    cz
    cz
    fnprg
    syl3anc
    @6
    @29
    @1
    @4
    wa
    @30
    @8
    @10
    wfn
    @31
    @2
    @1
    @5
    @4
    @25
    @26
    anim12i
    @32
    cc0
    c1
    cB
    cD
    cvv
    cvv
    cz
    cz
    fnprg
    syl3anc
    offvalfv
    @6
    @20
    cc0
    cA
    cB
    @9
    co
    #
    cop
    #
    c1
    cC
    cD
    @9
    co
    #
    cop
    #
    cpr
    @15
    @34
    @17
    @36
    @19
    @33
    @16
    cc0
    @9
    caddc
    cA
    cB
    caddc
    @9
    zringplusg
    eqcomi
    #
    oveqi
    opeq2i
    @35
    @18
    c1
    @9
    caddc
    cC
    cD
    @37
    oveqi
    opeq2i
    preq12i
    @6
    vx
    cc0
    c1
    @33
    @35
    @14
    cvv
    cvv
    cvv
    cvv
    @27
    @6
    c0ex
    a1i
    #
    @28
    @6
    1ex
    a1i
    #
    @6
    cA
    cB
    @9
    ovexd
    @6
    cC
    cD
    @9
    ovexd
    @11
    cc0
    wceq
    #
    @6
    @14
    cc0
    @7
    cfv
    #
    cc0
    @8
    cfv
    #
    @9
    co
    @33
    @40
    @12
    @41
    @13
    @42
    @9
    @11
    cc0
    @7
    fveq2
    @11
    cc0
    @8
    fveq2
    oveq12d
    @6
    @41
    cA
    @42
    cB
    @9
    @6
    @27
    @0
    @30
    @41
    cA
    wceq
    @38
    @2
    @0
    @5
    @23
    adantr
    @32
    cc0
    c1
    cA
    cC
    cvv
    cz
    fvpr1g
    syl3anc
    @6
    @27
    @1
    @30
    @42
    cB
    wceq
    @38
    @2
    @1
    @5
    @25
    adantr
    @32
    cc0
    c1
    cB
    cD
    cvv
    cz
    fvpr1g
    syl3anc
    oveq12d
    sylan9eqr
    @11
    c1
    wceq
    #
    @6
    @14
    c1
    @7
    cfv
    #
    c1
    @8
    cfv
    #
    @9
    co
    @35
    @43
    @12
    @44
    @13
    @45
    @9
    @11
    c1
    @7
    fveq2
    @11
    c1
    @8
    fveq2
    oveq12d
    @6
    @44
    cC
    @45
    cD
    @9
    @6
    @28
    @3
    @30
    @44
    cC
    wceq
    @39
    @5
    @3
    @2
    @24
    adantl
    @32
    cc0
    c1
    cA
    cC
    cvv
    cz
    fvpr2g
    syl3anc
    @6
    @28
    @4
    @30
    @45
    cD
    wceq
    @39
    @5
    @4
    @2
    @26
    adantl
    @32
    cc0
    c1
    cB
    cD
    cvv
    cz
    fvpr2g
    syl3anc
    oveq12d
    sylan9eqr
    fmptpr
    syl5reqr
    3eqtrd
end
