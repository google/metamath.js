include "cint.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "elintg.mm"
include "eleq2.mm"
include "rspccv.mm"
include "syl6bi.mm"
include "pm2.43i.mm"

theorem elinti
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. |^| B -> ( C e. B -> A e. C ) )

  proof
    cA
    cB
    cint
    #
    wcel
    #
    cC
    cB
    wcel
    cA
    cC
    wcel
    #
    wi
    #
    @1
    @1
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cB
    wral
    @3
    vx
    cA
    cB
    @0
    elintg
    @5
    @2
    vx
    cC
    cB
    @4
    cC
    cA
    eleq2
    rspccv
    syl6bi
    pm2.43i
end
