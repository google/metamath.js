include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "xpcomeng.mm"
include "pwen.mm"
include "syl.mm"
include "cvv.mm"
include "xpexg.mm"
include "ancoms.mm"
include "pw2eng.mm"
include "entr.mm"
include "syl2anc.mm"
include "enrefg.mm"
include "mapen.mm"
include "syl2anr.mm"
include "con0.mm"
include "2on.mm"
include "simpr.mm"
include "simpl.mm"
include "mapxpen.mm"
include "mp3an2i.mm"
include "ensymd.mm"

theorem enrelmap
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ~P ( A X. B ) ~~ ( ~P B ^m A ) )

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
    cxp
    #
    cpw
    #
    c2o
    cB
    cA
    cxp
    #
    cmap
    co
    #
    cen
    wbr
    #
    @6
    cB
    cpw
    #
    cA
    cmap
    co
    #
    cen
    wbr
    @4
    @9
    cen
    wbr
    @2
    @4
    @5
    cpw
    #
    cen
    wbr
    #
    @10
    @6
    cen
    wbr
    #
    @7
    @2
    @3
    @5
    cen
    wbr
    @11
    cA
    cB
    cV
    cW
    xpcomeng
    @3
    @5
    pwen
    syl
    @2
    @5
    cvv
    wcel
    #
    @12
    @1
    @0
    @13
    cB
    cA
    cW
    cV
    xpexg
    ancoms
    @5
    cvv
    pw2eng
    syl
    @4
    @10
    @6
    entr
    syl2anc
    @2
    @9
    @6
    @2
    @9
    c2o
    cB
    cmap
    co
    #
    cA
    cmap
    co
    #
    cen
    wbr
    #
    @15
    @6
    cen
    wbr
    #
    @9
    @6
    cen
    wbr
    @1
    @8
    @14
    cen
    wbr
    cA
    cA
    cen
    wbr
    @16
    @0
    cB
    cW
    pw2eng
    cA
    cV
    enrefg
    @8
    @14
    cA
    cA
    mapen
    syl2anr
    c2o
    con0
    wcel
    @2
    @1
    @0
    @17
    2on
    @0
    @1
    simpr
    @0
    @1
    simpl
    c2o
    cB
    cA
    con0
    cW
    cV
    mapxpen
    mp3an2i
    @9
    @15
    @6
    entr
    syl2anc
    ensymd
    @4
    @6
    @9
    entr
    syl2anc
end
