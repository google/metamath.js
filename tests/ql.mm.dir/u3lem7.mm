include "wn.mm"
include "wi3.mm"
include "wo.mm"
include "wa.mm"
include "comi31.mm"
include "comcom6.mm"
include "u3lemc4.mm"
include "df-i3.mm"
include "lor.mm"
include "or12.mm"
include "ax-a1.mm"
include "ran.mm"
include "2or.mm"
include "ax-r1.mm"
include "orabs.mm"
include "ax-a2.mm"
include "ax-r2.mm"

theorem u3lem7
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 ( a ' ->3 b ) ) = ( a ' v ( ( a ^ b ) v ( a ^ b ' ) ) )

  proof
    wva
    wva
    wn
    #
    wvb
    wi3
    #
    wi3
    @0
    @1
    wo
    #
    @0
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wa
    #
    wo
    #
    wo
    #
    wva
    @1
    wva
    @1
    @0
    wvb
    comi31
    comcom6
    u3lemc4
    @2
    @0
    @0
    wn
    #
    wvb
    wa
    #
    @8
    @4
    wa
    #
    wo
    #
    @0
    @8
    wvb
    wo
    #
    wa
    #
    wo
    #
    wo
    #
    @7
    @1
    @14
    @0
    @0
    wvb
    df-i3
    lor
    @15
    @11
    @0
    @13
    wo
    #
    wo
    #
    @7
    @0
    @11
    @13
    or12
    @17
    @6
    @0
    wo
    @7
    @11
    @6
    @16
    @0
    @6
    @11
    @3
    @9
    @5
    @10
    wva
    @8
    wvb
    wva
    ax-a1
    #
    ran
    wva
    @8
    @4
    @18
    ran
    2or
    ax-r1
    @0
    @12
    orabs
    2or
    @6
    @0
    ax-a2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
