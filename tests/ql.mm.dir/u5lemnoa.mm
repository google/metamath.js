include "wi5.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "u5lemana.mm"
include "ax-a2.mm"
include "anor3.mm"
include "anor2.mm"
include "2or.mm"
include "ax-r2.mm"
include "anor1.mm"
include "oran3.mm"
include "3tr2.mm"
include "con1.mm"

theorem u5lemnoa
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->5 b ) ' v a ) = ( ( a v b ) ^ ( a v b ' ) )

  proof
    wva
    wvb
    wi5
    #
    wn
    wva
    wo
    #
    wva
    wvb
    wo
    #
    wva
    wvb
    wn
    #
    wo
    #
    wa
    #
    @0
    wva
    wn
    #
    wa
    #
    @2
    wn
    #
    @4
    wn
    #
    wo
    #
    @1
    wn
    @5
    wn
    @7
    @6
    wvb
    wa
    #
    @6
    @3
    wa
    #
    wo
    #
    @10
    wva
    wvb
    u5lemana
    @13
    @12
    @11
    wo
    @10
    @11
    @12
    ax-a2
    @12
    @8
    @11
    @9
    wva
    wvb
    anor3
    wva
    wvb
    anor2
    2or
    ax-r2
    ax-r2
    @0
    wva
    anor1
    @2
    @4
    oran3
    3tr2
    con1
end
