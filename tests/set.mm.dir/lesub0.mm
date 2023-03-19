include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "0red.mm"
include "letri3.mm"
include "sylan2.mm"
include "ancom.mm"
include "simpr.mm"
include "simpl.mm"
include "lesub2.mm"
include "syl3anc.mm"
include "recnd.mm"
include "subid1d.mm"
include "breq1d.mm"
include "bitrd.mm"
include "ancoms.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "bitr2d.mm"

theorem lesub0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( 0 <_ A /\ B <_ ( B - A ) ) <-> A = 0 ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cc0
    wceq
    #
    cA
    cc0
    cle
    wbr
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    @5
    cB
    cB
    cA
    cmin
    co
    #
    cle
    wbr
    #
    wa
    #
    @1
    @0
    cc0
    cr
    wcel
    #
    @3
    @6
    wb
    @1
    0red
    cA
    cc0
    letri3
    sylan2
    @6
    @5
    @4
    wa
    @2
    @9
    @4
    @5
    ancom
    @2
    @4
    @8
    @5
    @1
    @0
    @4
    @8
    wb
    @1
    @0
    wa
    #
    @4
    cB
    cc0
    cmin
    co
    #
    @7
    cle
    wbr
    #
    @8
    @11
    @0
    @10
    @1
    @4
    @13
    wb
    @1
    @0
    simpr
    @11
    0red
    @1
    @0
    simpl
    #
    cA
    cc0
    cB
    lesub2
    syl3anc
    @11
    @12
    cB
    @7
    cle
    @11
    cB
    @11
    cB
    @14
    recnd
    subid1d
    breq1d
    bitrd
    ancoms
    anbi2d
    syl5bb
    bitr2d
end
