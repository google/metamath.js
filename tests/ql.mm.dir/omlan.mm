include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "lan.mm"
include "omla.mm"
include "ax-r2.mm"

theorem omlan
  let wva: term a
  let wvb: term b


  assert |- ( a ' ^ ( a v ( a ' ^ b ) ) ) = ( a ' ^ b )

  proof
    wva
    wn
    #
    wva
    @0
    wvb
    wa
    #
    wo
    #
    wa
    @0
    @0
    wn
    #
    @1
    wo
    #
    wa
    @1
    @2
    @4
    @0
    wva
    @3
    @1
    wva
    ax-a1
    ax-r5
    lan
    @0
    wvb
    omla
    ax-r2
end
