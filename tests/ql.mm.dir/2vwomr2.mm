include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "ancom.mm"
include "ax-a1.mm"
include "2an.mm"
include "ax-r2.mm"
include "lor.mm"
include "2or.mm"
include "ax-r1.mm"
include "ax-wom.mm"

theorem 2vwomr2
  let wva: term a
  let wvb: term b
  assume 2vwomr2.1: |- ( b v ( a ' ^ b ' ) ) = 1


  assert |- ( a ' v ( a ^ b ) ) = 1

  proof
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    @0
    wvb
    wn
    #
    wn
    #
    @0
    wn
    #
    wa
    #
    wo
    wt
    @1
    @5
    @0
    @1
    wvb
    wva
    wa
    @5
    wva
    wvb
    ancom
    wvb
    @3
    wva
    @4
    wvb
    ax-a1
    #
    wva
    ax-a1
    2an
    ax-r2
    lor
    @2
    @0
    @3
    @2
    @0
    wa
    #
    wo
    #
    wvb
    @0
    @2
    wa
    #
    wo
    #
    wt
    @10
    @8
    wvb
    @3
    @9
    @7
    @6
    @0
    @2
    ancom
    2or
    ax-r1
    2vwomr2.1
    ax-r2
    ax-wom
    ax-r2
end
