include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "ccda.mm"
include "co.mm"
include "c1o.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "pwcda1.mm"
include "syl.mm"
include "infcda1.mm"
include "pwen.mm"
include "entr.mm"
include "syl2anc.mm"

theorem pwcdaidm
  let cA: class A


  assert |- ( _om ~<_ A -> ( ~P A +c ~P A ) ~~ ~P A )

  proof
    com
    cA
    cdom
    wbr
    #
    cA
    cpw
    #
    @1
    ccda
    co
    #
    cA
    c1o
    ccda
    co
    #
    cpw
    #
    cen
    wbr
    #
    @4
    @1
    cen
    wbr
    #
    @2
    @1
    cen
    wbr
    @0
    cA
    cvv
    wcel
    @5
    com
    cA
    cdom
    reldom
    brrelex2i
    cA
    cvv
    pwcda1
    syl
    @0
    @3
    cA
    cen
    wbr
    @6
    cA
    infcda1
    @3
    cA
    pwen
    syl
    @2
    @4
    @1
    entr
    syl2anc
end
