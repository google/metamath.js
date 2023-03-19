include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "wt.mm"
include "df-i3.mm"
include "ax-r1.mm"
include "ax-r4.mm"
include "ax-r5.mm"
include "ska15.mm"
include "ax-r2.mm"

theorem mccune3
  param wva: term a
  param wvb: term b


  assert |- ( ( ( ( a ' ^ b ) v ( a ' ^ b ' ) ) v ( a ^ ( a ' v b ) ) ) ' v ( a ' v b ) ) = 1

  proof
    wva
    wn
    #
    wvb
    wa
    @0
    wvb
    wn
    wa
    wo
    wva
    @0
    wvb
    wo
    #
    wa
    wo
    #
    wn
    #
    @1
    wo
    wva
    wvb
    wi3
    #
    wn
    #
    @1
    wo
    wt
    @3
    @5
    @1
    @2
    @4
    @4
    @2
    wva
    wvb
    df-i3
    ax-r1
    ax-r4
    ax-r5
    wva
    wvb
    ska15
    ax-r2
end
