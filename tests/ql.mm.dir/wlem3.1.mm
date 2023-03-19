include "tb.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "wa.mm"
include "dfb.mm"
include "leoa.mm"
include "oran.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "con3.mm"
include "2or.mm"
include "ax-a2.mm"

theorem wlem3.1
  param wva: term a
  param wvb: term b
  assume wlem3.1.1: |- ( a v b ) = b
  assume wlem3.1.2: |- ( b ' v a ) = 1


  assert |- ( a == b ) = 1

  proof
    wva
    wvb
    tb
    #
    wvb
    wn
    #
    wva
    wo
    #
    wt
    @0
    wva
    wvb
    wa
    #
    wva
    wn
    @1
    wa
    #
    wo
    #
    @2
    wva
    wvb
    dfb
    @5
    wva
    @1
    wo
    @2
    @3
    wva
    @4
    @1
    wva
    wvb
    wvb
    wlem3.1.1
    leoa
    @4
    wvb
    @4
    wn
    #
    wva
    wvb
    wo
    #
    wvb
    @7
    @6
    wva
    wvb
    oran
    ax-r1
    wlem3.1.1
    ax-r2
    con3
    2or
    wva
    @1
    ax-a2
    ax-r2
    ax-r2
    wlem3.1.2
    ax-r2
end
