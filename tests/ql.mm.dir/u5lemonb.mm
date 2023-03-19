include "wi5.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i5.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "lear.mm"
include "df-le2.mm"
include "lor.mm"
include "ax-r2.mm"

theorem u5lemonb
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->5 b ) v b ' ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v b ' )

  proof
    wva
    wvb
    wi5
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
    @5
    @1
    wva
    wvb
    df-i5
    ax-r5
    @6
    @3
    @4
    @1
    wo
    #
    wo
    @7
    @3
    @4
    @1
    ax-a3
    @8
    @1
    @3
    @4
    @1
    @2
    @1
    lear
    df-le2
    lor
    ax-r2
    ax-r2
end
