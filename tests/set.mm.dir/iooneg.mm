include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "wb.mm"
include "ltneg.mm"
include "3adant2.mm"
include "ancoms.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo5.mm"
include "syl3an.mm"
include "renegcl.mm"
include "3com12.mm"
include "3bitr4d.mm"

theorem iooneg
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( C e. ( A (,) B ) <-> -u C e. ( -u B (,) -u A ) ) )

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
    cC
    clt
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    wa
    #
    cB
    cneg
    #
    cC
    cneg
    #
    clt
    wbr
    #
    @8
    cA
    cneg
    #
    clt
    wbr
    #
    wa
    #
    cC
    cA
    cB
    cioo
    co
    wcel
    #
    @8
    @7
    @10
    cioo
    co
    wcel
    #
    @3
    @6
    @11
    @9
    wa
    @12
    @3
    @4
    @11
    @5
    @9
    @0
    @2
    @4
    @11
    wb
    @1
    cA
    cC
    ltneg
    3adant2
    @1
    @2
    @5
    @9
    wb
    #
    @0
    @2
    @1
    @15
    cC
    cB
    ltneg
    ancoms
    3adant1
    anbi12d
    @11
    @9
    ancom
    syl6bb
    @0
    cA
    cxr
    wcel
    @1
    cB
    cxr
    wcel
    @2
    cC
    cxr
    wcel
    @13
    @6
    wb
    cA
    rexr
    cB
    rexr
    cC
    rexr
    cA
    cB
    cC
    elioo5
    syl3an
    @1
    @0
    @2
    @14
    @12
    wb
    #
    @1
    @7
    cr
    wcel
    #
    @0
    @10
    cr
    wcel
    #
    @2
    @8
    cr
    wcel
    #
    @16
    cB
    renegcl
    cA
    renegcl
    cC
    renegcl
    @17
    @7
    cxr
    wcel
    @18
    @10
    cxr
    wcel
    @19
    @8
    cxr
    wcel
    @16
    @7
    rexr
    @10
    rexr
    @8
    rexr
    @7
    @10
    @8
    elioo5
    syl3an
    syl3an
    3com12
    3bitr4d
end
