include "wt.mm"
include "tb.mm"
include "rbi.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "wr3.mm"

theorem wwbmp
  param wva: term a
  param wvb: term b
  assume wwbmp.1: |- a = 1
  assume wwbmp.2: |- ( a == b ) = 1


  assert |- b = 1

  proof
    wvb
    wt
    wvb
    tb
    #
    wva
    wvb
    tb
    #
    wt
    @1
    @0
    wva
    wt
    wvb
    wwbmp.1
    rbi
    ax-r1
    wwbmp.2
    ax-r2
    wr3
end
