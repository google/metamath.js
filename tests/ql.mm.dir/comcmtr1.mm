include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wcmtr.mm"
include "wt.mm"
include "df-c2.mm"
include "comcom3.mm"
include "2or.mm"
include "ax-r1.mm"
include "df-cmtr.mm"
include "df-t.mm"
include "3tr1.mm"

theorem comcmtr1
  param wva: term a
  param wvb: term b
  assume comcmtr1.1: |- a C b


  assert |- C ( a , b ) = 1

  proof
    wva
    wvb
    wa
    wva
    wvb
    wn
    #
    wa
    wo
    #
    wva
    wn
    #
    wvb
    wa
    @2
    @0
    wa
    wo
    #
    wo
    #
    wva
    @2
    wo
    #
    wva
    wvb
    wcmtr
    wt
    @5
    @4
    wva
    @1
    @2
    @3
    wva
    wvb
    comcmtr1.1
    df-c2
    @2
    wvb
    wva
    wvb
    comcmtr1.1
    comcom3
    df-c2
    2or
    ax-r1
    wva
    wvb
    df-cmtr
    wva
    df-t
    3tr1
end
