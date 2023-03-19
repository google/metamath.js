include "wo.mm"
include "wn.mm"
include "wf.mm"
include "ax-a1.mm"
include "or0.mm"
include "ax-r1.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "lor.mm"
include "ax-a5.mm"

theorem oridm
  param wva: term a


  assert |- ( a v a ) = a

  proof
    wva
    wva
    wo
    wva
    wva
    wn
    #
    wf
    wo
    #
    wn
    #
    wo
    wva
    wva
    @2
    wva
    wva
    @0
    wn
    @2
    wva
    ax-a1
    @0
    @1
    @1
    @0
    @0
    or0
    ax-r1
    ax-r4
    ax-r2
    lor
    wva
    wf
    ax-a5
    ax-r2
end
