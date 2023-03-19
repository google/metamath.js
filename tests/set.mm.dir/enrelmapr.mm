include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "xpcomeng.mm"
include "pwen.mm"
include "syl.mm"
include "enrelmap.mm"
include "ancoms.mm"
include "entr.mm"
include "syl2anc.mm"

theorem enrelmapr
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ~P ( A X. B ) ~~ ( ~P A ^m B ) )

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
    cB
    cA
    cxp
    #
    cpw
    #
    cen
    wbr
    #
    @6
    cA
    cpw
    cB
    cmap
    co
    #
    cen
    wbr
    #
    @4
    @8
    cen
    wbr
    @2
    @3
    @5
    cen
    wbr
    @7
    cA
    cB
    cV
    cW
    xpcomeng
    @3
    @5
    pwen
    syl
    @1
    @0
    @9
    cB
    cA
    cW
    cV
    enrelmap
    ancoms
    @4
    @6
    @8
    entr
    syl2anc
end
