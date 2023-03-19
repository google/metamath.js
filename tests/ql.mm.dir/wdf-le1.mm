include "wle2.mm"
include "wo.mm"
include "tb.mm"
include "wt.mm"
include "df-le.mm"
include "ax-r2.mm"

theorem wdf-le1
  let wva: term a
  let wvb: term b
  assume wdf-le1.1: |- ( ( a v b ) == b ) = 1


  assert |- ( a =<2 b ) = 1

  proof
    wva
    wvb
    wle2
    wva
    wvb
    wo
    wvb
    tb
    wt
    wva
    wvb
    df-le
    wdf-le1.1
    ax-r2
end
