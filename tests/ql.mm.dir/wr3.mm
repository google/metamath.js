include "wt.mm"
include "tb.mm"
include "1b.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem wr3
  param wva: term a
  assume wr3.1: |- ( 1 == a ) = 1


  assert |- a = 1

  proof
    wva
    wt
    wva
    tb
    #
    wt
    @0
    wva
    wva
    1b
    ax-r1
    wr3.1
    ax-r2
end
