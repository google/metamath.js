include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "wt.mm"
include "ax-a3.mm"
include "ax-a2.mm"
include "ancom.mm"
include "lecon.mm"
include "df2le2.mm"
include "ax-r2.mm"
include "sklem.mm"
include "lan.mm"
include "an1.mm"
include "2or.mm"
include "anor2.mm"
include "con2.mm"
include "3tr1.mm"
include "lor.mm"
include "df-i3.mm"
include "df-t.mm"

theorem lei3
  let wva: term a
  let wvb: term b
  assume lei3.1: |- a =< b


  assert |- ( a ->3 b ) = 1

  proof
    wva
    wn
    #
    wvb
    wa
    #
    @0
    wvb
    wn
    #
    wa
    #
    wo
    wva
    @0
    wvb
    wo
    #
    wa
    #
    wo
    #
    @1
    @1
    wn
    #
    wo
    #
    wva
    wvb
    wi3
    wt
    @6
    @1
    @3
    @5
    wo
    #
    wo
    @8
    @1
    @3
    @5
    ax-a3
    @9
    @7
    @1
    @2
    wva
    wo
    wva
    @2
    wo
    #
    @9
    @7
    @2
    wva
    ax-a2
    @3
    @2
    @5
    wva
    @3
    @2
    @0
    wa
    @2
    @0
    @2
    ancom
    @2
    @0
    wva
    wvb
    lei3.1
    lecon
    df2le2
    ax-r2
    @5
    wva
    wt
    wa
    wva
    @4
    wt
    wva
    wva
    wvb
    lei3.1
    sklem
    lan
    wva
    an1
    ax-r2
    2or
    @1
    @10
    wva
    wvb
    anor2
    con2
    3tr1
    lor
    ax-r2
    wva
    wvb
    df-i3
    @1
    df-t
    3tr1
end
