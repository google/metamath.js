include "wi4.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "u4lemc1.mm"
include "comcom.mm"
include "u4lemc4.mm"
include "u4lem1n.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "lear.mm"
include "leor.mm"
include "letr.mm"
include "df-le2.mm"
include "ax-a2.mm"
include "ax-r2.mm"

theorem u4lem2
  param wva: term a
  param wvb: term b


  assert |- ( ( ( a ->4 b ) ->4 a ) ->4 a ) = ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )

  proof
    wva
    wvb
    wi4
    #
    wva
    wi4
    #
    wva
    wi4
    @1
    wn
    #
    wva
    wo
    #
    wva
    wva
    wn
    #
    wvb
    wa
    @4
    wvb
    wn
    #
    wa
    wo
    #
    wo
    #
    @1
    wva
    wva
    @1
    @0
    wva
    u4lemc1
    comcom
    u4lemc4
    @3
    @4
    wvb
    wo
    @4
    @5
    wo
    wa
    #
    wva
    wa
    #
    @6
    wo
    #
    wva
    wo
    #
    @7
    @2
    @10
    wva
    wva
    wvb
    u4lem1n
    ax-r5
    @11
    @9
    @6
    wva
    wo
    #
    wo
    #
    @7
    @9
    @6
    wva
    ax-a3
    @13
    @12
    @7
    @9
    @12
    @9
    wva
    @12
    @8
    wva
    lear
    wva
    @6
    leor
    letr
    df-le2
    @6
    wva
    ax-a2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
