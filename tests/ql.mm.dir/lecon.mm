include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ax-a2.mm"
include "oran.mm"
include "df-le2.mm"
include "3tr2.mm"
include "con3.mm"
include "df2le1.mm"

theorem lecon
  let wva: term a
  let wvb: term b
  assume le.1: |- a =< b


  assert |- b ' =< a '

  proof
    wvb
    wn
    #
    wva
    wn
    #
    @0
    @1
    wa
    #
    wvb
    wvb
    wva
    wo
    wva
    wvb
    wo
    @2
    wn
    wvb
    wvb
    wva
    ax-a2
    wvb
    wva
    oran
    wva
    wvb
    le.1
    df-le2
    3tr2
    con3
    df2le1
end
