include "wn.mm"
include "wo.mm"
include "wi0.mm"
include "wt.mm"
include "df-i0.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "skr0.mm"

theorem lem3.3.2
  param wva: term a
  param wvb: term b
  assume lem3.3.2.1: |- a = 1
  assume lem3.3.2.2: |- ( a ->0 b ) = 1


  assert |- b = 1

  proof
    wva
    wvb
    lem3.3.2.1
    wva
    wn
    wvb
    wo
    #
    wva
    wvb
    wi0
    #
    wt
    @1
    @0
    wva
    wvb
    df-i0
    ax-r1
    lem3.3.2.2
    ax-r2
    skr0
end
