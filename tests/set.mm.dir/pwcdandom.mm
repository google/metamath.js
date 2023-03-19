include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "ccda.mm"
include "co.mm"
include "cxp.mm"
include "pwxpndom2.mm"
include "wi.mm"
include "c1o.mm"
include "cen.mm"
include "c0.mm"
include "csn.mm"
include "df1o2.mm"
include "xpeq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "0ex.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "syl5eqbr.mm"
include "ensymd.mm"
include "wss.mm"
include "omex.mm"
include "word.mm"
include "ordom.mm"
include "1onn.mm"
include "ordelss.mm"
include "mp2an.mm"
include "ssdomg.mm"
include "mp2.mm"
include "domtr.mm"
include "mpan.mm"
include "xpdom2g.mm"
include "syl2anc.mm"
include "endomtr.mm"
include "cdadom2.mm"
include "expcom.mm"
include "3syl.mm"
include "mtod.mm"

theorem pwcdandom
  let cA: class A


  assert |- ( _om ~<_ A -> -. ~P A ~<_ ( A +c A ) )

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
    ccda
    co
    #
    cdom
    wbr
    #
    @1
    cA
    cA
    cA
    cxp
    #
    ccda
    co
    #
    cdom
    wbr
    #
    cA
    pwxpndom2
    @0
    cA
    @4
    cdom
    wbr
    #
    @2
    @5
    cdom
    wbr
    #
    @3
    @6
    wi
    @0
    cA
    cA
    c1o
    cxp
    #
    cen
    wbr
    @9
    @4
    cdom
    wbr
    #
    @7
    @0
    @9
    cA
    @0
    @9
    cA
    c0
    csn
    #
    cxp
    #
    cA
    cen
    c1o
    @11
    cA
    df1o2
    xpeq2i
    @0
    cA
    cvv
    wcel
    #
    c0
    cvv
    wcel
    @12
    cA
    cen
    wbr
    com
    cA
    cdom
    reldom
    brrelex2i
    #
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    syl5eqbr
    ensymd
    @0
    @13
    c1o
    cA
    cdom
    wbr
    #
    @10
    @14
    c1o
    com
    cdom
    wbr
    #
    @0
    @15
    com
    cvv
    wcel
    c1o
    com
    wss
    #
    @16
    omex
    com
    word
    c1o
    com
    wcel
    @17
    ordom
    1onn
    com
    c1o
    ordelss
    mp2an
    c1o
    com
    cvv
    ssdomg
    mp2
    c1o
    com
    cA
    domtr
    mpan
    c1o
    cA
    cA
    cvv
    xpdom2g
    syl2anc
    cA
    @9
    @4
    endomtr
    syl2anc
    cA
    @4
    cA
    cdadom2
    @3
    @8
    @6
    @1
    @2
    @5
    domtr
    expcom
    3syl
    mtod
end
