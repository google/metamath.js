include "cpr.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "wo.mm"
include "elex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "elprg.mm"
include "pm5.21nii.mm"

theorem elpr2
  let cA: class A
  let cB: class B
  let cC: class C
  assume elpr2.1: |- B e. _V
  assume elpr2.2: |- C e. _V


  assert |- ( A e. { B , C } <-> ( A = B \/ A = C ) )

  proof
    cA
    cB
    cC
    cpr
    #
    wcel
    cA
    cvv
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    wo
    cA
    @0
    elex
    @2
    @1
    @3
    @2
    @1
    cB
    cvv
    wcel
    elpr2.1
    cA
    cB
    cvv
    eleq1
    mpbiri
    @3
    @1
    cC
    cvv
    wcel
    elpr2.2
    cA
    cC
    cvv
    eleq1
    mpbiri
    jaoi
    cA
    cB
    cC
    cvv
    elprg
    pm5.21nii
end
