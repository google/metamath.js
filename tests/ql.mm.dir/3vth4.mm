include "wo.mm"
include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "3vth2.mm"
include "ax-a1.mm"
include "ran.mm"
include "3tr2.mm"
include "lor.mm"
include "df-i2.mm"
include "3tr1.mm"

theorem 3vth4
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 b ) ' ->2 ( b v c ) ) = ( ( a ->2 c ) ' ->2 ( b v c ) )

  proof
    wvb
    wvc
    wo
    #
    wva
    wvb
    wi2
    #
    wn
    #
    wn
    #
    @0
    wn
    #
    wa
    #
    wo
    @0
    wva
    wvc
    wi2
    #
    wn
    #
    wn
    #
    @4
    wa
    #
    wo
    @2
    @0
    wi2
    @7
    @0
    wi2
    @5
    @9
    @0
    @1
    @4
    wa
    @6
    @4
    wa
    @5
    @9
    wva
    wvb
    wvc
    3vth2
    @1
    @3
    @4
    @1
    ax-a1
    ran
    @6
    @8
    @4
    @6
    ax-a1
    ran
    3tr2
    lor
    @2
    @0
    df-i2
    @7
    @0
    df-i2
    3tr1
end
