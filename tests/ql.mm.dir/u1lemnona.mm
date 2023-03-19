include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "u1lemaa.mm"
include "df-a.mm"
include "3tr2.mm"
include "con1.mm"

theorem u1lemnona
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->1 b ) ' v a ' ) = ( a ' v b ' )

  proof
    wva
    wvb
    wi1
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
    u1lemaa
    @0
    wva
    df-a
    wva
    wvb
    df-a
    3tr2
    con1
end
