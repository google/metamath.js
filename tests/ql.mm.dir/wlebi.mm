include "wo.mm"
include "wdf-le2.mm"
include "wr1.mm"
include "ax-a2.mm"
include "bi1.mm"
include "wr2.mm"

theorem wlebi
  let wva: term a
  let wvb: term b
  assume wlebi.1: |- ( a =<2 b ) = 1
  assume wlebi.2: |- ( b =<2 a ) = 1


  assert |- ( a == b ) = 1

  proof
    wva
    wva
    wvb
    wo
    #
    wvb
    wva
    wvb
    wva
    wo
    #
    @0
    @1
    wva
    wvb
    wva
    wlebi.2
    wdf-le2
    wr1
    @1
    @0
    wvb
    wva
    ax-a2
    bi1
    wr2
    wva
    wvb
    wlebi.1
    wdf-le2
    wr2
end
