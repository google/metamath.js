include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "wi1.mm"
include "oran.mm"
include "ax-r1.mm"
include "orabs.mm"
include "ax-r2.mm"
include "con3.mm"
include "lor.mm"
include "lea.mm"
include "df-le2.mm"
include "ax-r5.mm"
include "womaa.mm"
include "df-i3.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom13
  param wva: term a
  param wvb: term b


  assert |- ( a ->3 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wa
    #
    @0
    @1
    wn
    wa
    #
    wo
    #
    wva
    @0
    @1
    wo
    #
    wa
    #
    wo
    #
    @5
    wva
    @1
    wi3
    wva
    wvb
    wi1
    @7
    @0
    @6
    wo
    @5
    @4
    @0
    @6
    @4
    @2
    @0
    wo
    @0
    @3
    @0
    @2
    @3
    wva
    @3
    wn
    #
    wva
    @1
    wo
    #
    wva
    @9
    @8
    wva
    @1
    oran
    ax-r1
    wva
    wvb
    orabs
    ax-r2
    con3
    lor
    @2
    @0
    @0
    @1
    lea
    df-le2
    ax-r2
    ax-r5
    wva
    wvb
    womaa
    ax-r2
    wva
    @1
    df-i3
    wva
    wvb
    df-i1
    3tr1
end
