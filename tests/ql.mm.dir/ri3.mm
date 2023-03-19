include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "ax-r4.mm"
include "ran.mm"
include "2or.mm"
include "ax-r5.mm"
include "2an.mm"
include "df-i3.mm"
include "3tr1.mm"

theorem ri3
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ri3.1: |- a = b


  assert |- ( a ->3 c ) = ( b ->3 c )

  proof
    wva
    wn
    #
    wvc
    wa
    #
    @0
    wvc
    wn
    #
    wa
    #
    wo
    #
    wva
    @0
    wvc
    wo
    #
    wa
    #
    wo
    wvb
    wn
    #
    wvc
    wa
    #
    @7
    @2
    wa
    #
    wo
    #
    wvb
    @7
    wvc
    wo
    #
    wa
    #
    wo
    wva
    wvc
    wi3
    wvb
    wvc
    wi3
    @4
    @10
    @6
    @12
    @1
    @8
    @3
    @9
    @0
    @7
    wvc
    wva
    wvb
    ri3.1
    ax-r4
    #
    ran
    @0
    @7
    @2
    @13
    ran
    2or
    wva
    wvb
    @5
    @11
    ri3.1
    @0
    @7
    wvc
    @13
    ax-r5
    2an
    2or
    wva
    wvc
    df-i3
    wvb
    wvc
    df-i3
    3tr1
end
