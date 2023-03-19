include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i2.mm"
include "wi1.mm"
include "df-i1.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "ax-wom.mm"

theorem 2vwomr1a
  let wva: term a
  let wvb: term b
  assume 2vwomr1a.1: |- ( a ->1 b ) = 1


  assert |- ( a ->2 b ) = 1

  proof
    wva
    wvb
    wi2
    wvb
    wva
    wn
    #
    wvb
    wn
    wa
    wo
    wt
    wva
    wvb
    df-i2
    wva
    wvb
    @0
    wva
    wvb
    wa
    wo
    #
    wva
    wvb
    wi1
    #
    wt
    @2
    @1
    wva
    wvb
    df-i1
    ax-r1
    2vwomr1a.1
    ax-r2
    ax-wom
    ax-r2
end
