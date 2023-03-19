include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "simpl.mm"
include "nelelne.mm"
include "ancld.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem difsn
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( -. A e. B -> ( B \ { A } ) = B )

  proof
    cA
    cB
    wcel
    wn
    #
    vx
    cB
    cA
    csn
    cdif
    #
    cB
    vx
    cv
    #
    @1
    wcel
    @2
    cB
    wcel
    #
    @2
    cA
    wne
    #
    wa
    #
    @0
    @3
    @2
    cB
    cA
    eldifsn
    @0
    @5
    @3
    @3
    @4
    simpl
    @0
    @3
    @4
    cA
    cB
    @2
    nelelne
    ancld
    impbid2
    syl5bb
    eqrdv
end
