include "cdom.mm"
include "wbr.mm"
include "ccda.mm"
include "co.mm"
include "cdadom1.mm"
include "cen.mm"
include "wb.mm"
include "cdacomen.mm"
include "domen1.mm"
include "domen2.mm"
include "sylan9bb.mm"
include "mp2an.mm"
include "sylib.mm"

theorem cdadom2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~<_ B -> ( C +c A ) ~<_ ( C +c B ) )

  proof
    cA
    cB
    cdom
    wbr
    cA
    cC
    ccda
    co
    #
    cB
    cC
    ccda
    co
    #
    cdom
    wbr
    #
    cC
    cA
    ccda
    co
    #
    cC
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    cA
    cB
    cC
    cdadom1
    @0
    @3
    cen
    wbr
    #
    @1
    @4
    cen
    wbr
    #
    @2
    @5
    wb
    cA
    cC
    cdacomen
    cB
    cC
    cdacomen
    @6
    @2
    @3
    @1
    cdom
    wbr
    @7
    @5
    @0
    @3
    @1
    domen1
    @1
    @4
    @3
    domen2
    sylan9bb
    mp2an
    sylib
end
