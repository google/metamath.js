include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-a.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "ax-r5.mm"
include "ax-r4.mm"
include "ax-r2.mm"

theorem anor2
  param wva: term a
  param wvb: term b


  assert |- ( a ' ^ b ) = ( a v b ' ) '

  proof
    wva
    wn
    #
    wvb
    wa
    @0
    wn
    #
    wvb
    wn
    #
    wo
    #
    wn
    wva
    @2
    wo
    #
    wn
    @0
    wvb
    df-a
    @3
    @4
    @1
    wva
    @2
    wva
    @1
    wva
    ax-a1
    ax-r1
    ax-r5
    ax-r4
    ax-r2
end
