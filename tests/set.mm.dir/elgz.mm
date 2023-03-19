include "cgz.mm"
include "wcel.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cz.mm"
include "cim.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "df-gz.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem elgz
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Z[i] <-> ( A e. CC /\ ( Re ` A ) e. ZZ /\ ( Im ` A ) e. ZZ ) )

  proof
    cA
    cgz
    wcel
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cz
    wcel
    #
    cA
    cim
    cfv
    #
    cz
    wcel
    #
    wa
    #
    wa
    @0
    @2
    @4
    w3a
    vx
    cv
    #
    cre
    cfv
    #
    cz
    wcel
    #
    @6
    cim
    cfv
    #
    cz
    wcel
    #
    wa
    @5
    vx
    cA
    cc
    cgz
    @6
    cA
    wceq
    #
    @8
    @2
    @10
    @4
    @11
    @7
    @1
    cz
    @6
    cA
    cre
    fveq2
    eleq1d
    @11
    @9
    @3
    cz
    @6
    cA
    cim
    fveq2
    eleq1d
    anbi12d
    vx
    df-gz
    elrab2
    @0
    @2
    @4
    3anass
    bitr4i
end
