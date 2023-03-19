include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cun.mm"
include "ccda.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelexi.mm"
include "uncdadom.mm"
include "syl2an.mm"
include "cdadom1.mm"
include "cdadom2.mm"
include "domtr.mm"
include "cxp.mm"
include "cen.mm"
include "wss.mm"
include "omex.mm"
include "xpex.mm"
include "c2o.mm"
include "wceq.mm"
include "xp2cda.mm"
include "ax-mp.mm"
include "word.mm"
include "ordom.mm"
include "2onn.mm"
include "ordelss.mm"
include "mp2an.mm"
include "xpss2.mm"
include "eqsstr3i.mm"
include "ssdomg.mm"
include "mp2.mm"
include "xpomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "syl2anc.mm"

theorem unctb
  let cA: class A
  let cB: class B


  assert |- ( ( A ~<_ _om /\ B ~<_ _om ) -> ( A u. B ) ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    cB
    com
    cdom
    wbr
    #
    wa
    #
    cA
    cB
    cun
    #
    cA
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    @4
    com
    cdom
    wbr
    #
    @3
    com
    cdom
    wbr
    @0
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @5
    @1
    cA
    com
    cdom
    reldom
    brrelexi
    cB
    com
    cdom
    reldom
    brrelexi
    cA
    cB
    cvv
    cvv
    uncdadom
    syl2an
    @2
    @4
    com
    com
    ccda
    co
    #
    cdom
    wbr
    #
    @7
    com
    cdom
    wbr
    #
    @6
    @0
    @4
    com
    cB
    ccda
    co
    #
    cdom
    wbr
    @10
    @7
    cdom
    wbr
    @8
    @1
    cA
    com
    cB
    cdadom1
    cB
    com
    com
    cdadom2
    @4
    @10
    @7
    domtr
    syl2an
    @7
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @11
    com
    cen
    wbr
    @9
    @11
    cvv
    wcel
    @7
    @11
    wss
    @12
    com
    com
    omex
    omex
    xpex
    @7
    com
    c2o
    cxp
    #
    @11
    com
    cvv
    wcel
    @13
    @7
    wceq
    omex
    com
    cvv
    xp2cda
    ax-mp
    c2o
    com
    wss
    #
    @13
    @11
    wss
    com
    word
    c2o
    com
    wcel
    @14
    ordom
    2onn
    com
    c2o
    ordelss
    mp2an
    c2o
    com
    com
    xpss2
    ax-mp
    eqsstr3i
    @7
    @11
    cvv
    ssdomg
    mp2
    xpomen
    @7
    @11
    com
    domentr
    mp2an
    @4
    @7
    com
    domtr
    sylancl
    @3
    @4
    com
    domtr
    syl2anc
end
