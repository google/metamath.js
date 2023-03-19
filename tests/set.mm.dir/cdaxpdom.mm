include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cdom.mm"
include "cen.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "cdaval.mm"
include "syl2an.mm"
include "wb.mm"
include "0ex.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "sdomen2.mm"
include "syl.mm"
include "ibir.mm"
include "con0.mm"
include "1on.mm"
include "unxpdom.mm"
include "eqbrtrd.mm"
include "xpen.mm"
include "domentr.mm"
include "syl2anc.mm"

theorem cdaxpdom
  let cA: class A
  let cB: class B


  assert |- ( ( 1o ~< A /\ 1o ~< B ) -> ( A +c B ) ~<_ ( A X. B ) )

  proof
    c1o
    cA
    csdm
    wbr
    #
    c1o
    cB
    csdm
    wbr
    #
    wa
    #
    cA
    cB
    ccda
    co
    #
    cA
    c0
    csn
    cxp
    #
    cB
    c1o
    csn
    cxp
    #
    cxp
    #
    cdom
    wbr
    @6
    cA
    cB
    cxp
    #
    cen
    wbr
    #
    @3
    @7
    cdom
    wbr
    @2
    @3
    @4
    @5
    cun
    #
    @6
    cdom
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @3
    @9
    wceq
    @1
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    #
    c1o
    cB
    csdm
    relsdom
    brrelex2i
    #
    cA
    cB
    cvv
    cvv
    cdaval
    syl2an
    @0
    c1o
    @4
    csdm
    wbr
    #
    c1o
    @5
    csdm
    wbr
    #
    @9
    @6
    cdom
    wbr
    @1
    @0
    @14
    @0
    @4
    cA
    cen
    wbr
    #
    @14
    @0
    wb
    @0
    @10
    c0
    cvv
    wcel
    @16
    @12
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    #
    @4
    cA
    c1o
    sdomen2
    syl
    ibir
    @1
    @15
    @1
    @5
    cB
    cen
    wbr
    #
    @15
    @1
    wb
    @1
    @11
    c1o
    con0
    wcel
    @18
    @13
    1on
    cB
    c1o
    cvv
    con0
    xpsneng
    sylancl
    #
    @5
    cB
    c1o
    sdomen2
    syl
    ibir
    @4
    @5
    unxpdom
    syl2an
    eqbrtrd
    @0
    @16
    @18
    @8
    @1
    @17
    @19
    @4
    cA
    @5
    cB
    xpen
    syl2an
    @3
    @6
    @7
    domentr
    syl2anc
end
