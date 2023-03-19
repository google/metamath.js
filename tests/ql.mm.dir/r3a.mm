include "wt.mm"
include "tb.mm"
include "wn.mm"
include "wo.mm"
include "df-t.mm"
include "df-b.mm"
include "3tr2.mm"
include "ax-r3.mm"

theorem r3a
  let wva: term a
  let wvb: term b
  assume r3a.1: |- 1 = ( a == b )


  assert |- a = b

  proof
    wva
    wvb
    wva
    wt
    wva
    wvb
    tb
    wva
    wva
    wn
    #
    wo
    @0
    wvb
    wn
    wo
    wn
    wva
    wvb
    wo
    wn
    wo
    r3a.1
    wva
    df-t
    wva
    wvb
    df-b
    3tr2
    ax-r3
end
