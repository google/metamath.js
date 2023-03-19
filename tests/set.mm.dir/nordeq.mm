include "word.mm"
include "wcel.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "ordirr.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "necon2ad.mm"
include "imp.mm"

theorem nordeq
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ B e. A ) -> A =/= B )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    cA
    cB
    wne
    @0
    @1
    cA
    cB
    @0
    cA
    cA
    wcel
    #
    wn
    cA
    cB
    wceq
    #
    @1
    wn
    cA
    ordirr
    @3
    @2
    @1
    cA
    cB
    cA
    eleq1
    notbid
    syl5ibcom
    necon2ad
    imp
end
