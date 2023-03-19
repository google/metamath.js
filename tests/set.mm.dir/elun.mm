include "cun.mm"
include "wcel.mm"
include "cvv.mm"
include "wo.mm"
include "elex.mm"
include "jaoi.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "orbi12d.mm"
include "df-un.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elun
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. ( B u. C ) <-> ( A e. B \/ A e. C ) )

  proof
    cA
    cB
    cC
    cun
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
    wo
    #
    cA
    @0
    elex
    @2
    @1
    @3
    cA
    cB
    elex
    cA
    cC
    elex
    jaoi
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
    wo
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
    orbi12d
    vx
    cB
    cC
    df-un
    elab2g
    pm5.21nii
end
