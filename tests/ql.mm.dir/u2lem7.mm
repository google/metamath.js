include "wn.mm"
include "wi2.mm"
include "wa.mm"
include "wo.mm"
include "df-i2.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "ran.mm"
include "lor.mm"
include "ax-r2.mm"
include "ancom.mm"
include "u2lemnaa.mm"
include "2or.mm"
include "ax-a3.mm"
include "ax-a2.mm"

theorem u2lem7
  let wva: term a
  let wvb: term b


  assert |- ( a ->2 ( a ' ->2 b ) ) = ( ( ( a ^ b ' ) v ( a ' ^ b ' ) ) v b )

  proof
    wva
    wva
    wn
    #
    wvb
    wi2
    #
    wi2
    @1
    @0
    @1
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wn
    #
    wa
    #
    @0
    @5
    wa
    #
    wo
    #
    wvb
    wo
    #
    wva
    @1
    df-i2
    @4
    wvb
    @6
    wo
    #
    @7
    wo
    #
    @9
    @1
    @10
    @3
    @7
    @1
    wvb
    @0
    wn
    #
    @5
    wa
    #
    wo
    @10
    @0
    wvb
    df-i2
    @13
    @6
    wvb
    @12
    wva
    @5
    wva
    @12
    wva
    ax-a1
    ax-r1
    ran
    lor
    ax-r2
    @3
    @2
    @0
    wa
    @7
    @0
    @2
    ancom
    @0
    wvb
    u2lemnaa
    ax-r2
    2or
    @11
    wvb
    @8
    wo
    @9
    wvb
    @6
    @7
    ax-a3
    wvb
    @8
    ax-a2
    ax-r2
    ax-r2
    ax-r2
end
