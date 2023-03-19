include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "cplusg.mm"
include "cfv.mm"
include "caddc.mm"
include "zsubcl.mm"
include "simpr.mm"
include "jca.mm"
include "eqid.mm"
include "zlmodzxzadd.mm"
include "syl2an.mm"
include "cc.mm"
include "zcn.mm"
include "npcan.mm"
include "adantr.mm"
include "opeq2d.mm"
include "adantl.mm"
include "preq12d.mm"
include "eqtrd.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "clmod.mm"
include "zring.mm"
include "csca.mm"
include "zlmodzxzlmod.mm"
include "lmodgrp.mm"
include "mp1i.mm"
include "zlmodzxzel.mm"
include "ad2ant2r.mm"
include "grpsubadd.mm"
include "syl13anc.mm"
include "mpbird.mm"

theorem zlmodzxzsub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.mi: class .-
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume zlmodzxz.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzsub.m: |- .- = ( -g ` Z )


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) ) -> ( { <. 0 , A >. , <. 1 , C >. } .- { <. 0 , B >. , <. 1 , D >. } ) = { <. 0 , ( A - B ) >. , <. 1 , ( C - D ) >. } )

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
    #
    c1
    cC
    cop
    #
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
    c.mi
    co
    cc0
    cA
    cB
    cmin
    co
    #
    cop
    c1
    cC
    cD
    cmin
    co
    #
    cop
    cpr
    #
    wceq
    #
    @13
    @10
    cZ
    cplusg
    cfv
    #
    co
    #
    @9
    wceq
    #
    @6
    @16
    cc0
    @11
    cB
    caddc
    co
    #
    cop
    #
    c1
    @12
    cD
    caddc
    co
    #
    cop
    #
    cpr
    #
    @9
    @2
    @11
    cz
    wcel
    #
    @1
    wa
    @12
    cz
    wcel
    #
    @4
    wa
    @16
    @22
    wceq
    @5
    @2
    @23
    @1
    cA
    cB
    zsubcl
    #
    @0
    @1
    simpr
    #
    jca
    @5
    @24
    @4
    cC
    cD
    zsubcl
    #
    @3
    @4
    simpr
    #
    jca
    @11
    cB
    @12
    cD
    @15
    cZ
    zlmodzxz.z
    @15
    eqid
    #
    zlmodzxzadd
    syl2an
    @6
    @19
    @7
    @21
    @8
    @6
    @18
    cA
    cc0
    @2
    @18
    cA
    wceq
    #
    @5
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @30
    @1
    cA
    zcn
    cB
    zcn
    cA
    cB
    npcan
    syl2an
    adantr
    opeq2d
    @6
    @20
    cC
    c1
    @5
    @20
    cC
    wceq
    #
    @2
    @3
    cC
    cc
    wcel
    cD
    cc
    wcel
    @31
    @4
    cC
    zcn
    cD
    zcn
    cC
    cD
    npcan
    syl2an
    adantl
    opeq2d
    preq12d
    eqtrd
    @6
    cZ
    cgrp
    wcel
    #
    @9
    cZ
    cbs
    cfv
    #
    wcel
    #
    @10
    @33
    wcel
    #
    @13
    @33
    wcel
    #
    @14
    @17
    wb
    cZ
    clmod
    wcel
    #
    zring
    cZ
    csca
    cfv
    wceq
    #
    wa
    @32
    @6
    cZ
    zlmodzxz.z
    zlmodzxzlmod
    @37
    @32
    @38
    cZ
    lmodgrp
    adantr
    mp1i
    @0
    @3
    @34
    @1
    @4
    cA
    cC
    cZ
    zlmodzxz.z
    zlmodzxzel
    ad2ant2r
    @2
    @1
    @4
    @35
    @5
    @26
    @28
    cB
    cD
    cZ
    zlmodzxz.z
    zlmodzxzel
    syl2an
    @2
    @23
    @24
    @36
    @5
    @25
    @27
    @11
    @12
    cZ
    zlmodzxz.z
    zlmodzxzel
    syl2an
    @33
    @15
    cZ
    c.mi
    @9
    @10
    @13
    @33
    eqid
    @29
    zlmodzxzsub.m
    grpsubadd
    syl13anc
    mpbird
end
