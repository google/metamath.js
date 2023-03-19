include "wa.mm"
include "wn.mm"
include "wo.mm"
include "ax-a3.mm"
include "df-a.mm"
include "con2.mm"
include "ax-r5.mm"
include "lor.mm"
include "3tr1.mm"
include "ax-r4.mm"

theorem anass
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ^ b ) ^ c ) = ( a ^ ( b ^ c ) )

  proof
    wva
    wvb
    wa
    #
    wn
    #
    wvc
    wn
    #
    wo
    #
    wn
    wva
    wn
    #
    wvb
    wvc
    wa
    #
    wn
    #
    wo
    #
    wn
    @0
    wvc
    wa
    wva
    @5
    wa
    @3
    @7
    @4
    wvb
    wn
    #
    wo
    #
    @2
    wo
    @4
    @8
    @2
    wo
    #
    wo
    @3
    @7
    @4
    @8
    @2
    ax-a3
    @1
    @9
    @2
    @0
    @9
    wva
    wvb
    df-a
    con2
    ax-r5
    @6
    @10
    @4
    @5
    @10
    wvb
    wvc
    df-a
    con2
    lor
    3tr1
    ax-r4
    @0
    wvc
    df-a
    wva
    @5
    df-a
    3tr1
end
