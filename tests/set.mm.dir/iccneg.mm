include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wb.mm"
include "renegcl.mm"
include "ax-1.mm"
include "impbid2.mm"
include "3ad2ant3.mm"
include "ancom.mm"
include "leneg.mm"
include "ancoms.mm"
include "3adant1.mm"
include "3adant2.mm"
include "anbi12d.mm"
include "syl5bbr.mm"
include "elicc2.mm"
include "3adant3.mm"
include "3anass.mm"
include "syl6bb.mm"
include "syl2anr.mm"
include "3bitr4d.mm"

theorem iccneg
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( C e. ( A [,] B ) <-> -u C e. ( -u B [,] -u A ) ) )

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
    @2
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cC
    cneg
    #
    cr
    wcel
    #
    cB
    cneg
    #
    @8
    cle
    wbr
    #
    @8
    cA
    cneg
    #
    cle
    wbr
    #
    wa
    #
    wa
    #
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    @8
    @10
    @12
    cicc
    co
    wcel
    #
    @3
    @2
    @9
    @6
    @14
    @2
    @0
    @2
    @9
    wb
    @1
    @2
    @2
    @9
    cC
    renegcl
    @2
    @9
    ax-1
    impbid2
    3ad2ant3
    @6
    @5
    @4
    wa
    @3
    @14
    @5
    @4
    ancom
    @3
    @5
    @11
    @4
    @13
    @1
    @2
    @5
    @11
    wb
    #
    @0
    @2
    @1
    @18
    cC
    cB
    leneg
    ancoms
    3adant1
    @0
    @2
    @4
    @13
    wb
    @1
    cA
    cC
    leneg
    3adant2
    anbi12d
    syl5bbr
    anbi12d
    @3
    @16
    @2
    @4
    @5
    w3a
    #
    @7
    @0
    @1
    @16
    @19
    wb
    @2
    cA
    cB
    cC
    elicc2
    3adant3
    @2
    @4
    @5
    3anass
    syl6bb
    @3
    @17
    @9
    @11
    @13
    w3a
    #
    @15
    @0
    @1
    @17
    @20
    wb
    #
    @2
    @1
    @10
    cr
    wcel
    @12
    cr
    wcel
    @21
    @0
    cB
    renegcl
    cA
    renegcl
    @10
    @12
    @8
    elicc2
    syl2anr
    3adant3
    @9
    @11
    @13
    3anass
    syl6bb
    3bitr4d
end
