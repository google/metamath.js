include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cltrr.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "ax-pre-lttrn.mm"
include "wb.mm"
include "ltxrlt.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3adant2.mm"
include "3imtr4d.mm"

theorem axlttrn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A < B /\ B < C ) -> A < C ) )

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
    cltrr
    wbr
    #
    cB
    cC
    cltrr
    wbr
    #
    wa
    cA
    cC
    cltrr
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    cA
    cC
    clt
    wbr
    #
    cA
    cB
    cC
    ax-pre-lttrn
    @3
    @7
    @4
    @8
    @5
    @0
    @1
    @7
    @4
    wb
    @2
    cA
    cB
    ltxrlt
    3adant3
    @1
    @2
    @8
    @5
    wb
    @0
    cB
    cC
    ltxrlt
    3adant1
    anbi12d
    @0
    @2
    @9
    @6
    wb
    @1
    cA
    cC
    ltxrlt
    3adant2
    3imtr4d
end
