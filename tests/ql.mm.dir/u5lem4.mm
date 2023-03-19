include "wi5.mm"
include "wn.mm"
include "wo.mm"
include "u5lemc1.mm"
include "u5lemc4.mm"
include "wa.mm"
include "u5lem3.mm"
include "lor.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "oridm.mm"
include "ax-r5.mm"
include "ax-r2.mm"

theorem u5lem4
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 ( a ->5 ( b ->5 a ) ) ) = ( a ->5 ( b ->5 a ) )

  proof
    wva
    wva
    wvb
    wva
    wi5
    #
    wi5
    #
    wi5
    wva
    wn
    #
    @1
    wo
    #
    @1
    wva
    @1
    wva
    @0
    u5lemc1
    u5lemc4
    @3
    @2
    @2
    wva
    wvb
    wa
    wva
    wvb
    wn
    wa
    wo
    #
    wo
    #
    wo
    #
    @1
    @1
    @5
    @2
    wva
    wvb
    u5lem3
    #
    lor
    @6
    @2
    @2
    wo
    #
    @4
    wo
    #
    @1
    @9
    @6
    @2
    @2
    @4
    ax-a3
    ax-r1
    @9
    @5
    @1
    @8
    @2
    @4
    @2
    oridm
    ax-r5
    @1
    @5
    @7
    ax-r1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
