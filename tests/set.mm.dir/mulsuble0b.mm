include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "resubcl.mm"
include "3adant3.mm"
include "ancoms.mm"
include "3adant1.mm"
include "mulle0b.mm"
include "syl2anc.mm"
include "suble0.mm"
include "subge0.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "orbi12d.mm"
include "bitrd.mm"

theorem mulsuble0b
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( ( A - B ) x. ( C - B ) ) <_ 0 <-> ( ( A <_ B /\ B <_ C ) \/ ( C <_ B /\ B <_ A ) ) ) )

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
    cA
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    cmul
    co
    cc0
    cle
    wbr
    #
    @4
    cc0
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    cc0
    @4
    cle
    wbr
    #
    @5
    cc0
    cle
    wbr
    #
    wa
    #
    wo
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    wa
    #
    cC
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wa
    #
    wo
    @3
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @6
    @13
    wb
    @0
    @1
    @20
    @2
    cA
    cB
    resubcl
    3adant3
    @1
    @2
    @21
    @0
    @2
    @1
    @21
    cC
    cB
    resubcl
    ancoms
    3adant1
    @4
    @5
    mulle0b
    syl2anc
    @3
    @9
    @16
    @12
    @19
    @3
    @7
    @14
    @8
    @15
    @0
    @1
    @7
    @14
    wb
    @2
    cA
    cB
    suble0
    3adant3
    @1
    @2
    @8
    @15
    wb
    #
    @0
    @2
    @1
    @22
    cC
    cB
    subge0
    ancoms
    3adant1
    anbi12d
    @3
    @12
    @18
    @17
    wa
    @19
    @3
    @10
    @18
    @11
    @17
    @0
    @1
    @10
    @18
    wb
    @2
    cA
    cB
    subge0
    3adant3
    @1
    @2
    @11
    @17
    wb
    #
    @0
    @2
    @1
    @23
    cC
    cB
    suble0
    ancoms
    3adant1
    anbi12d
    @18
    @17
    ancom
    syl6bb
    orbi12d
    bitrd
end
