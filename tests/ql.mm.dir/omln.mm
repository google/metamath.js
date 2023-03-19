include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ax-a1.mm"
include "ran.mm"
include "lor.mm"
include "oml.mm"
include "ax-r2.mm"

theorem omln
  let wva: term a
  let wvb: term b


  assert |- ( a ' v ( a ^ ( a ' v b ) ) ) = ( a ' v b )

  proof
    wva
    wn
    #
    wva
    @0
    wvb
    wo
    #
    wa
    #
    wo
    @0
    @0
    wn
    #
    @1
    wa
    #
    wo
    @1
    @2
    @4
    @0
    wva
    @3
    @1
    wva
    ax-a1
    ran
    lor
    @0
    wvb
    oml
    ax-r2
end
