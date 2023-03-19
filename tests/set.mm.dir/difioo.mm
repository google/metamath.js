include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "cioo.mm"
include "co.mm"
include "cdif.mm"
include "cico.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "cun.mm"
include "incom.mm"
include "joiniooico.mm"
include "anassrs.mm"
include "simpld.mm"
include "syl5eqr.mm"
include "simprd.mm"
include "uncom.mm"
include "a1i.mm"
include "wss.mm"
include "simpll1.mm"
include "simpl3.mm"
include "adantr.mm"
include "xrleid.mm"
include "syl.mm"
include "simpr.mm"
include "ioossioo.mm"
include "syl22anc.mm"
include "ssequn2.mm"
include "sylib.mm"
include "3eqtr4d.mm"
include "difeq.mm"
include "sylanbrc.mm"
include "simpl2.mm"
include "xrltle.mm"
include "imp.mm"
include "syl21anc.mm"
include "ssdif0.mm"
include "ico0.mm"
include "biimpar.mm"
include "eqtr4d.mm"
include "wo.mm"
include "xrlelttric.mm"
include "syl2anc.mm"
include "mpjaodan.mm"

theorem difioo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A < B ) -> ( ( A (,) C ) \ ( A (,) B ) ) = ( B [,) C ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    cB
    cC
    cle
    wbr
    #
    cA
    cC
    cioo
    co
    #
    cA
    cB
    cioo
    co
    #
    cdif
    #
    cB
    cC
    cico
    co
    #
    wceq
    #
    cC
    cB
    clt
    wbr
    #
    @5
    @6
    wa
    #
    @10
    @8
    cin
    #
    c0
    wceq
    @10
    @8
    cun
    #
    @7
    @8
    cun
    #
    wceq
    @11
    @13
    @14
    @8
    @10
    cin
    #
    c0
    @8
    @10
    incom
    @13
    @17
    c0
    wceq
    #
    @8
    @10
    cun
    #
    @7
    wceq
    #
    @3
    @4
    @6
    @18
    @20
    wa
    cA
    cB
    cC
    joiniooico
    anassrs
    #
    simpld
    syl5eqr
    @13
    @19
    @7
    @15
    @16
    @13
    @18
    @20
    @21
    simprd
    @15
    @19
    wceq
    @13
    @10
    @8
    uncom
    a1i
    @13
    @8
    @7
    wss
    #
    @16
    @7
    wceq
    @13
    @0
    @2
    cA
    cA
    cle
    wbr
    #
    @6
    @22
    @0
    @1
    @2
    @4
    @6
    simpll1
    #
    @5
    @2
    @6
    @0
    @1
    @2
    @4
    simpl3
    #
    adantr
    @13
    @0
    @23
    @24
    cA
    xrleid
    #
    syl
    @5
    @6
    simpr
    cA
    cC
    cA
    cB
    ioossioo
    syl22anc
    @8
    @7
    ssequn2
    sylib
    3eqtr4d
    @7
    @8
    @10
    difeq
    sylanbrc
    @5
    @12
    wa
    #
    @9
    c0
    @10
    @27
    @7
    @8
    wss
    #
    @9
    c0
    wceq
    @27
    @0
    @1
    @23
    cC
    cB
    cle
    wbr
    #
    @28
    @0
    @1
    @2
    @4
    @12
    simpll1
    #
    @5
    @1
    @12
    @0
    @1
    @2
    @4
    simpl2
    #
    adantr
    #
    @27
    @0
    @23
    @30
    @26
    syl
    @27
    @2
    @1
    @12
    @29
    @5
    @2
    @12
    @25
    adantr
    #
    @32
    @5
    @12
    simpr
    @2
    @1
    wa
    @12
    @29
    cC
    cB
    xrltle
    imp
    syl21anc
    #
    cA
    cB
    cA
    cC
    ioossioo
    syl22anc
    @7
    @8
    ssdif0
    sylib
    @27
    @1
    @2
    @29
    @10
    c0
    wceq
    #
    @32
    @33
    @34
    @1
    @2
    wa
    @35
    @29
    cB
    cC
    ico0
    biimpar
    syl21anc
    eqtr4d
    @5
    @1
    @2
    @6
    @12
    wo
    @31
    @25
    cB
    cC
    xrlelttric
    syl2anc
    mpjaodan
end
