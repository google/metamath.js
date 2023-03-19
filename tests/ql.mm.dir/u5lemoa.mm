include "wi5.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "df-i5.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "lor.mm"
include "ax-r1.mm"
include "orabs.mm"
include "ax-r2.mm"

theorem u5lemoa
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->5 b ) v a ) = ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )

  proof
    wva
    wvb
    wi5
    #
    wva
    wo
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    @2
    wvb
    wn
    wa
    #
    wo
    #
    wva
    wo
    #
    wva
    @3
    @4
    wo
    #
    wo
    #
    @0
    @5
    wva
    wva
    wvb
    df-i5
    ax-r5
    @6
    wva
    @5
    wo
    #
    @8
    @5
    wva
    ax-a2
    @9
    wva
    @1
    @7
    wo
    #
    wo
    #
    @8
    @5
    @10
    wva
    @1
    @3
    @4
    ax-a3
    lor
    @11
    wva
    @1
    wo
    #
    @7
    wo
    #
    @8
    @13
    @11
    wva
    @1
    @7
    ax-a3
    ax-r1
    @12
    wva
    @7
    wva
    wvb
    orabs
    ax-r5
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
