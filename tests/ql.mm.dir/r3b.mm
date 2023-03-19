include "wt.mm"
include "tb.mm"
include "wn.mm"
include "wo.mm"
include "df-t.mm"
include "ax-r2.mm"
include "1b.mm"
include "wed.mm"

theorem r3b
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume r3b.1: |- ( c v c ' ) = ( a == b )


  assert |- a = b

  proof
    wt
    wva
    wvb
    tb
    #
    wva
    wvb
    wt
    wvc
    wvc
    wn
    wo
    @0
    wvc
    df-t
    r3b.1
    ax-r2
    @0
    1b
    wed
end
