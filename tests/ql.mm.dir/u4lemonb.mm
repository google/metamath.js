include "wi4.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i4.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "lear.mm"
include "df-le2.mm"
include "lor.mm"
include "ax-r2.mm"

theorem u4lemonb
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) v b ' ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v b ' )

  proof
    wva
    wvb
    wi4
    #
    wvb
    wn
    #
    wo
    wva
    wvb
    wa
    wva
    wn
    #
    wvb
    wa
    wo
    #
    @2
    wvb
    wo
    #
    @1
    wa
    #
    wo
    #
    @1
    wo
    #
    @3
    @1
    wo
    #
    @0
    @6
    @1
    wva
    wvb
    df-i4
    ax-r5
    @7
    @3
    @5
    @1
    wo
    #
    wo
    @8
    @3
    @5
    @1
    ax-a3
    @9
    @1
    @3
    @5
    @1
    @4
    @1
    lear
    df-le2
    lor
    ax-r2
    ax-r2
end
