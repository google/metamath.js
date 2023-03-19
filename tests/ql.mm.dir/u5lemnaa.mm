include "wi5.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor2.mm"
include "u5lemona.mm"
include "ax-r4.mm"
include "anor1.mm"
include "ax-r1.mm"
include "df-a.mm"
include "con2.mm"
include "lan.mm"
include "ax-r2.mm"

theorem u5lemnaa
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->5 b ) ' ^ a ) = ( a ^ ( a ' v b ' ) )

  proof
    wva
    wvb
    wi5
    #
    wn
    wva
    wa
    @0
    wva
    wn
    #
    wo
    #
    wn
    #
    wva
    @1
    wvb
    wn
    wo
    #
    wa
    #
    @0
    wva
    anor2
    @3
    @1
    wva
    wvb
    wa
    #
    wo
    #
    wn
    #
    @5
    @2
    @7
    wva
    wvb
    u5lemona
    ax-r4
    @8
    wva
    @6
    wn
    #
    wa
    #
    @5
    @10
    @8
    wva
    @6
    anor1
    ax-r1
    @9
    @4
    wva
    @6
    @4
    wva
    wvb
    df-a
    con2
    lan
    ax-r2
    ax-r2
    ax-r2
end
