include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "enrelmap.mm"
include "ensymd.mm"
include "enrelmapr.mm"
include "entr.mm"
include "syl2anc.mm"

theorem enmappw
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( ~P B ^m A ) ~~ ( ~P A ^m B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cB
    cpw
    cA
    cmap
    co
    #
    cA
    cB
    cxp
    cpw
    #
    cen
    wbr
    @2
    cA
    cpw
    cB
    cmap
    co
    #
    cen
    wbr
    @1
    @3
    cen
    wbr
    @0
    @2
    @1
    cA
    cB
    cV
    cW
    enrelmap
    ensymd
    cA
    cB
    cV
    cW
    enrelmapr
    @1
    @2
    @3
    entr
    syl2anc
end
