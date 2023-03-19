include "wcel.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "cpw.mm"
include "c2o.mm"
include "cmap.mm"
include "cen.mm"
include "wbr.mm"
include "cxp.mm"
include "ovex.mm"
include "pw2en.mm"
include "con0.mm"
include "2on.mm"
include "mapcdaen.mm"
include "mp3an1.mm"
include "wb.mm"
include "pw2eng.mm"
include "xpen.mm"
include "syl2an.mm"
include "enen2.mm"
include "syl.mm"
include "mpbird.mm"
include "entr.mm"
include "sylancr.mm"

theorem pwcdaen
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ~P ( A +c B ) ~~ ( ~P A X. ~P B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    ccda
    co
    #
    cpw
    #
    c2o
    @3
    cmap
    co
    #
    cen
    wbr
    @5
    cA
    cpw
    #
    cB
    cpw
    #
    cxp
    #
    cen
    wbr
    #
    @4
    @8
    cen
    wbr
    @3
    cA
    cB
    ccda
    ovex
    pw2en
    @2
    @9
    @5
    c2o
    cA
    cmap
    co
    #
    c2o
    cB
    cmap
    co
    #
    cxp
    #
    cen
    wbr
    #
    c2o
    con0
    wcel
    @0
    @1
    @13
    2on
    c2o
    cA
    cB
    con0
    cV
    cW
    mapcdaen
    mp3an1
    @2
    @8
    @12
    cen
    wbr
    #
    @9
    @13
    wb
    @0
    @6
    @10
    cen
    wbr
    @7
    @11
    cen
    wbr
    @14
    @1
    cA
    cV
    pw2eng
    cB
    cW
    pw2eng
    @6
    @10
    @7
    @11
    xpen
    syl2an
    @8
    @12
    @5
    enen2
    syl
    mpbird
    @4
    @5
    @8
    entr
    sylancr
end
