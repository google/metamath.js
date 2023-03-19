include "wo.mm"
include "df-le2.mm"
include "ax-r1.mm"
include "ax-a2.mm"
include "ax-r2.mm"

theorem lebi
  let wva: term a
  let wvb: term b
  assume lebi.1: |- a =< b
  assume lebi.2: |- b =< a


  assert |- a = b

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
    lebi.2
    df-le2
    ax-r1
    wvb
    wva
    ax-a2
    ax-r2
    wva
    wvb
    lebi.1
    df-le2
    ax-r2
end
