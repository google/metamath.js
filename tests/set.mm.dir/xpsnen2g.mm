include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "snex.mm"
include "xpcomeng.mm"
include "mpan.mm"
include "adantl.mm"
include "xpsneng.mm"
include "ancoms.mm"
include "entr.mm"
include "syl2anc.mm"

theorem xpsnen2g
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( { A } X. B ) ~~ B )

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
    cA
    csn
    #
    cB
    cxp
    #
    cB
    @2
    cxp
    #
    cen
    wbr
    #
    @4
    cB
    cen
    wbr
    #
    @3
    cB
    cen
    wbr
    @1
    @5
    @0
    @2
    cvv
    wcel
    @1
    @5
    cA
    snex
    @2
    cB
    cvv
    cW
    xpcomeng
    mpan
    adantl
    @1
    @0
    @6
    cB
    cA
    cW
    cV
    xpsneng
    ancoms
    @3
    @4
    cB
    entr
    syl2anc
end
