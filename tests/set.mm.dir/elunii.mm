include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "cuni.mm"
include "wceq.mm"
include "eleq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "anabsi7.mm"
include "eluni.mm"
include "sylibr.mm"

theorem elunii
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. B /\ B e. C ) -> A e. U. C )

  proof
    cA
    cB
    wcel
    #
    cB
    cC
    wcel
    #
    wa
    #
    cA
    vx
    cv
    #
    wcel
    #
    @3
    cC
    wcel
    #
    wa
    #
    vx
    wex
    #
    cA
    cC
    cuni
    wcel
    @0
    @1
    @7
    @6
    @2
    vx
    cB
    cC
    @3
    cB
    wceq
    @4
    @0
    @5
    @1
    @3
    cB
    cA
    eleq2
    @3
    cB
    cC
    eleq1
    anbi12d
    spcegv
    anabsi7
    vx
    cA
    cC
    eluni
    sylibr
end
