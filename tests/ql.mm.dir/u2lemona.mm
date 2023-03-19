include "wi2.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i2.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "ax-a2.mm"
include "lea.mm"
include "df-le2.mm"
include "ax-r2.mm"

theorem u2lemona
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) v a ' ) = ( a ' v b )

  proof
    wva
    wvb
    wi2
    #
    wva
    wn
    #
    wo
    wvb
    @1
    wvb
    wn
    #
    wa
    #
    wo
    #
    @1
    wo
    #
    @1
    wvb
    wo
    #
    @0
    @4
    @1
    wva
    wvb
    df-i2
    ax-r5
    @5
    wvb
    @3
    @1
    wo
    #
    wo
    #
    @6
    wvb
    @3
    @1
    ax-a3
    @8
    @7
    wvb
    wo
    @6
    wvb
    @7
    ax-a2
    @7
    @1
    wvb
    @3
    @1
    @1
    @2
    lea
    df-le2
    ax-r5
    ax-r2
    ax-r2
    ax-r2
end
