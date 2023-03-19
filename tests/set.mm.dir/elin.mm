include "cin.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "adantl.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "df-in.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elin
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. ( B i^i C ) <-> ( A e. B /\ A e. C ) )

  proof
    cA
    cB
    cC
    cin
    #
    wcel
    cA
    cvv
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wa
    #
    cA
    @0
    elex
    @3
    @1
    @2
    cA
    cC
    elex
    adantl
    vx
    cv
    #
    cB
    wcel
    #
    @5
    cC
    wcel
    #
    wa
    @4
    vx
    cA
    @0
    cvv
    @5
    cA
    wceq
    @6
    @2
    @7
    @3
    @5
    cA
    cB
    eleq1
    @5
    cA
    cC
    eleq1
    anbi12d
    vx
    cB
    cC
    df-in
    elab2g
    pm5.21nii
end
