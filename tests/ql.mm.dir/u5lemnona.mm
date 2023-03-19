include "wi5.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "u5lemaa.mm"
include "df-a.mm"
include "3tr2.mm"
include "con1.mm"

theorem u5lemnona
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->5 b ) ' v a ' ) = ( a ' v b ' )

  proof
    wva
    wvb
    wi5
    #
    wn
    wva
    wn
    #
    wo
    #
    @1
    wvb
    wn
    wo
    #
    @0
    wva
    wa
    wva
    wvb
    wa
    @2
    wn
    @3
    wn
    wva
    wvb
    u5lemaa
    @0
    wva
    df-a
    wva
    wvb
    df-a
    3tr2
    con1
end
