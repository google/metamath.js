include "word.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "csuc.mm"
include "cv.mm"
include "wral.mm"
include "ordunisuc2.mm"
include "biimpa.mm"
include "suceq.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "ex.mm"
include "wi.mm"
include "wtr.mm"
include "ordtr.mm"
include "trsuc.mm"
include "syl.mm"
include "adantr.mm"
include "impbid.mm"

theorem limsuc2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( Ord A /\ A = U. A ) -> ( B e. A <-> suc B e. A ) )

  proof
    cA
    word
    #
    cA
    cA
    cuni
    wceq
    #
    wa
    #
    cB
    cA
    wcel
    #
    cB
    csuc
    #
    cA
    wcel
    #
    @2
    @3
    @5
    @2
    vx
    cv
    #
    csuc
    #
    cA
    wcel
    #
    vx
    cA
    wral
    #
    @3
    @5
    @0
    @1
    @9
    vx
    cA
    ordunisuc2
    biimpa
    @8
    @5
    vx
    cB
    cA
    @6
    cB
    wceq
    @7
    @4
    cA
    @6
    cB
    suceq
    eleq1d
    rspccva
    sylan
    ex
    @0
    @5
    @3
    wi
    #
    @1
    @0
    cA
    wtr
    #
    @10
    cA
    ordtr
    @11
    @5
    @3
    cA
    cB
    trsuc
    ex
    syl
    adantr
    impbid
end
