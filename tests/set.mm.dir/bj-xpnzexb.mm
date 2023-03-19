include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "bj-xpexg2.mm"
include "wne.mm"
include "wi.mm"
include "eldifsni.mm"
include "bj-xpnzex.mm"
include "syl.mm"
include "impbid.mm"

theorem bj-xpnzexb
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. ( V \ { (/) } ) -> ( B e. _V <-> ( A X. B ) e. _V ) )

  proof
    cA
    cV
    c0
    csn
    cdif
    #
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    cxp
    cvv
    wcel
    #
    cA
    cB
    @0
    cvv
    bj-xpexg2
    @1
    cA
    c0
    wne
    @3
    @2
    wi
    cA
    cV
    c0
    eldifsni
    cA
    cB
    cvv
    bj-xpnzex
    syl
    impbid
end
