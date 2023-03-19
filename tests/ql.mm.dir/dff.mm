include "wf.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "dff2.mm"
include "ancom.mm"
include "anor2.mm"
include "ax-r2.mm"
include "ax-r1.mm"

theorem dff
  let wva: term a


  assert |- 0 = ( a ^ a ' )

  proof
    wf
    wva
    wva
    wn
    #
    wo
    wn
    #
    wva
    @0
    wa
    #
    wva
    dff2
    @2
    @1
    @2
    @0
    wva
    wa
    @1
    wva
    @0
    ancom
    wva
    wva
    anor2
    ax-r2
    ax-r1
    ax-r2
end
