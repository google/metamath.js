include "cv.mm"
include "wfo.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "foeq2.mm"
include "breq2.mm"
include "imbi12d.mm"
include "vex.mm"
include "fodom.mm"
include "vtoclg.mm"

theorem fodomg
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x


  assert |- ( A e. C -> ( F : A -onto-> B -> B ~<_ A ) )

  proof
    vx
    cv
    #
    cB
    cF
    wfo
    #
    cB
    @0
    cdom
    wbr
    #
    wi
    cA
    cB
    cF
    wfo
    #
    cB
    cA
    cdom
    wbr
    #
    wi
    vx
    cA
    cC
    @0
    cA
    wceq
    @1
    @3
    @2
    @4
    @0
    cA
    cB
    cF
    foeq2
    @0
    cA
    cB
    cdom
    breq2
    imbi12d
    @0
    cB
    cF
    vx
    vex
    fodom
    vtoclg
end
