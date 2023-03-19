include "wo.mm"
include "tb.mm"
include "wle2.mm"
include "wt.mm"
include "df-le.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem wdf-le2
  param wva: term a
  param wvb: term b
  assume wdf-le2.1: |- ( a =<2 b ) = 1


  assert |- ( ( a v b ) == b ) = 1

  proof
    wva
    wvb
    wo
    wvb
    tb
    #
    wva
    wvb
    wle2
    #
    wt
    @1
    @0
    wva
    wvb
    df-le
    ax-r1
    wdf-le2.1
    ax-r2
end
