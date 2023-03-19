include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "orbi2i.mm"
include "orbi1i.mm"
include "orass.mm"
include "bitr2i.mm"
include "3bitrri.mm"
include "uneqri.mm"

theorem unass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A u. B ) u. C ) = ( A u. ( B u. C ) )

  proof
    vx
    cA
    cB
    cun
    #
    cC
    cA
    cB
    cC
    cun
    #
    cun
    #
    vx
    cv
    #
    @2
    wcel
    @3
    cA
    wcel
    #
    @3
    @1
    wcel
    #
    wo
    @4
    @3
    cB
    wcel
    #
    @3
    cC
    wcel
    #
    wo
    #
    wo
    #
    @3
    @0
    wcel
    #
    @7
    wo
    #
    @3
    cA
    @1
    elun
    @5
    @8
    @4
    @3
    cB
    cC
    elun
    orbi2i
    @11
    @4
    @6
    wo
    #
    @7
    wo
    @9
    @10
    @12
    @7
    @3
    cA
    cB
    elun
    orbi1i
    @4
    @6
    @7
    orass
    bitr2i
    3bitrri
    uneqri
end
