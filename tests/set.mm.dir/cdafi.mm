include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "cdaval.mm"
include "syl2an.mm"
include "cen.mm"
include "wb.mm"
include "con0.mm"
include "0elon.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "sdomen1.mm"
include "syl.mm"
include "ibir.mm"
include "1on.mm"
include "unfi2.mm"
include "eqbrtrd.mm"

theorem cdafi
  let cA: class A
  let cB: class B


  assert |- ( ( A ~< _om /\ B ~< _om ) -> ( A +c B ) ~< _om )

  proof
    cA
    com
    csdm
    wbr
    #
    cB
    com
    csdm
    wbr
    #
    wa
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
    cun
    #
    com
    csdm
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @2
    @5
    wceq
    @1
    cA
    com
    csdm
    relsdom
    brrelexi
    #
    cB
    com
    csdm
    relsdom
    brrelexi
    #
    cA
    cB
    cvv
    cvv
    cdaval
    syl2an
    @0
    @3
    com
    csdm
    wbr
    #
    @4
    com
    csdm
    wbr
    #
    @5
    com
    csdm
    wbr
    @1
    @0
    @10
    @0
    @3
    cA
    cen
    wbr
    #
    @10
    @0
    wb
    @0
    @6
    c0
    con0
    wcel
    @12
    @8
    0elon
    cA
    c0
    cvv
    con0
    xpsneng
    sylancl
    @3
    cA
    com
    sdomen1
    syl
    ibir
    @1
    @11
    @1
    @4
    cB
    cen
    wbr
    #
    @11
    @1
    wb
    @1
    @7
    c1o
    con0
    wcel
    @13
    @9
    1on
    cB
    c1o
    cvv
    con0
    xpsneng
    sylancl
    @4
    cB
    com
    sdomen1
    syl
    ibir
    @3
    @4
    unfi2
    syl2an
    eqbrtrd
end
