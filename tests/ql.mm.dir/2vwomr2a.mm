include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i1.mm"
include "wi2.mm"
include "df-i2.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "2vwomr2.mm"

theorem 2vwomr2a
  param wva: term a
  param wvb: term b
  assume 2vwomr2a.1: |- ( a ->2 b ) = 1


  assert |- ( a ->1 b ) = 1

  proof
    wva
    wvb
    wi1
    wva
    wn
    #
    wva
    wvb
    wa
    wo
    wt
    wva
    wvb
    df-i1
    wva
    wvb
    wvb
    @0
    wvb
    wn
    wa
    wo
    #
    wva
    wvb
    wi2
    #
    wt
    @2
    @1
    wva
    wvb
    df-i2
    ax-r1
    2vwomr2a.1
    ax-r2
    2vwomr2
    ax-r2
end
