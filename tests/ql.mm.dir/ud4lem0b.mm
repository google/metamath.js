include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "ran.mm"
include "ax-r4.mm"
include "2or.mm"
include "ax-r5.mm"
include "df-i4.mm"
include "3tr1.mm"

theorem ud4lem0b
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ud4lem0a.1: |- a = b


  assert |- ( a ->4 c ) = ( b ->4 c )

  proof
    wva
    wvc
    wa
    #
    wva
    wn
    #
    wvc
    wa
    #
    wo
    #
    @1
    wvc
    wo
    #
    wvc
    wn
    #
    wa
    #
    wo
    wvb
    wvc
    wa
    #
    wvb
    wn
    #
    wvc
    wa
    #
    wo
    #
    @8
    wvc
    wo
    #
    @5
    wa
    #
    wo
    wva
    wvc
    wi4
    wvb
    wvc
    wi4
    @3
    @10
    @6
    @12
    @0
    @7
    @2
    @9
    wva
    wvb
    wvc
    ud4lem0a.1
    ran
    @1
    @8
    wvc
    wva
    wvb
    ud4lem0a.1
    ax-r4
    #
    ran
    2or
    @4
    @11
    @5
    @1
    @8
    wvc
    @13
    ax-r5
    ran
    2or
    wva
    wvc
    df-i4
    wvb
    wvc
    df-i4
    3tr1
end
