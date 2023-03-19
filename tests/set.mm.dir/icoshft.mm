include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "caddc.mm"
include "wi.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "elico2.mm"
include "sylan2.mm"
include "biimpd.mm"
include "3adant3.mm"
include "3anass.mm"
include "syl6ib.mm"
include "leadd1.mm"
include "3com12.mm"
include "3expib.mm"
include "com12.mm"
include "3adant2.mm"
include "imp.mm"
include "ltadd1.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "pm5.32da.mm"
include "readdcl.mm"
include "expcom.mm"
include "anim1d.mm"
include "syl6ibr.mm"
include "3ad2ant3.mm"
include "biimprd.mm"
include "syl2anc.mm"
include "syld.mm"
include "sylbid.mm"

theorem icoshft
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( X e. ( A [,) B ) -> ( X + C ) e. ( ( A + C ) [,) ( B + C ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cX
    cA
    cB
    cico
    co
    wcel
    #
    cX
    cr
    wcel
    #
    cA
    cX
    cle
    wbr
    #
    cX
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cX
    cC
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    cico
    co
    wcel
    #
    @3
    @4
    @5
    @6
    @7
    w3a
    #
    @9
    @0
    @1
    @4
    @14
    wi
    @2
    @0
    @1
    wa
    @4
    @14
    @1
    @0
    cB
    cxr
    wcel
    @4
    @14
    wb
    cB
    rexr
    cA
    cB
    cX
    elico2
    sylan2
    biimpd
    3adant3
    @5
    @6
    @7
    3anass
    syl6ib
    @3
    @9
    @5
    @11
    @10
    cle
    wbr
    #
    @10
    @12
    clt
    wbr
    #
    wa
    #
    wa
    #
    @13
    @3
    @5
    @8
    @17
    @3
    @5
    wa
    @6
    @15
    @7
    @16
    @3
    @5
    @6
    @15
    wb
    #
    @0
    @2
    @5
    @19
    wi
    @1
    @5
    @0
    @2
    wa
    @19
    @5
    @0
    @2
    @19
    @0
    @5
    @2
    @19
    cA
    cX
    cC
    leadd1
    3com12
    3expib
    com12
    3adant2
    imp
    @3
    @5
    @7
    @16
    wb
    #
    @1
    @2
    @5
    @20
    wi
    @0
    @5
    @1
    @2
    wa
    @20
    @5
    @1
    @2
    @20
    cX
    cB
    cC
    ltadd1
    3expib
    com12
    3adant1
    imp
    anbi12d
    pm5.32da
    @3
    @18
    @10
    cr
    wcel
    #
    @15
    @16
    w3a
    #
    @13
    @2
    @0
    @18
    @22
    wi
    @1
    @2
    @18
    @21
    @17
    wa
    @22
    @2
    @5
    @21
    @17
    @5
    @2
    @21
    cX
    cC
    readdcl
    expcom
    anim1d
    @21
    @15
    @16
    3anass
    syl6ibr
    3ad2ant3
    @3
    @11
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @22
    @13
    wi
    @0
    @2
    @23
    @1
    cA
    cC
    readdcl
    3adant2
    @1
    @2
    @24
    @0
    cB
    cC
    readdcl
    3adant1
    @23
    @24
    wa
    @13
    @22
    @24
    @23
    @12
    cxr
    wcel
    @13
    @22
    wb
    @12
    rexr
    @11
    @12
    @10
    elico2
    sylan2
    biimprd
    syl2anc
    syld
    sylbid
    syld
end
