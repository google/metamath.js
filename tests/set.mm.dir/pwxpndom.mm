include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "cxp.mm"
include "ccda.mm"
include "co.mm"
include "pwxpndom2.mm"
include "wi.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "cdadom3.mm"
include "cdacomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "domtr.mm"
include "expcom.mm"
include "syl.mm"
include "mtod.mm"

theorem pwxpndom
  let cA: class A


  assert |- ( _om ~<_ A -> -. ~P A ~<_ ( A X. A ) )

  proof
    com
    cA
    cdom
    wbr
    #
    cA
    cpw
    #
    cA
    cA
    cxp
    #
    cdom
    wbr
    #
    @1
    cA
    @2
    ccda
    co
    #
    cdom
    wbr
    #
    cA
    pwxpndom2
    @0
    @2
    @4
    cdom
    wbr
    #
    @3
    @5
    wi
    @0
    @2
    @2
    cA
    ccda
    co
    #
    cdom
    wbr
    #
    @7
    @4
    cen
    wbr
    @6
    @0
    @2
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @8
    @0
    @10
    @10
    @9
    com
    cA
    cdom
    reldom
    brrelex2i
    #
    @11
    cA
    cA
    cvv
    cvv
    xpexg
    syl2anc
    @11
    @2
    cA
    cvv
    cvv
    cdadom3
    syl2anc
    @2
    cA
    cdacomen
    @2
    @7
    @4
    domentr
    sylancl
    @3
    @6
    @5
    @1
    @2
    @4
    domtr
    expcom
    syl
    mtod
end
