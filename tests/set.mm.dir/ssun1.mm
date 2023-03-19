include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "orc.mm"
include "elun.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem ssun1
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- A C_ ( A u. B )

  proof
    vx
    cA
    cA
    cB
    cun
    #
    vx
    cv
    #
    cA
    wcel
    #
    @2
    @1
    cB
    wcel
    #
    wo
    @1
    @0
    wcel
    @2
    @3
    orc
    @1
    cA
    cB
    elun
    sylibr
    ssriv
end
