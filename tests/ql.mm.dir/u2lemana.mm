include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i2.mm"
include "ran.mm"
include "ax-a2.mm"
include "coman1.mm"
include "coman2.mm"
include "comcom7.mm"
include "fh2r.mm"
include "an32.mm"
include "anidm.mm"
include "ax-r2.mm"
include "ancom.mm"
include "2or.mm"

theorem u2lemana
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ^ a ' ) = ( ( a ' ^ b ) v ( a ' ^ b ' ) )

  proof
    wva
    wvb
    wi2
    #
    wva
    wn
    #
    wa
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
    wa
    #
    @1
    wvb
    wa
    #
    @3
    wo
    #
    @0
    @4
    @1
    wva
    wvb
    df-i2
    ran
    @5
    @3
    wvb
    wo
    #
    @1
    wa
    #
    @7
    @4
    @8
    @1
    wvb
    @3
    ax-a2
    ran
    @9
    @3
    @1
    wa
    #
    wvb
    @1
    wa
    #
    wo
    #
    @7
    @3
    @1
    wvb
    @1
    @2
    coman1
    @3
    wvb
    @1
    @2
    coman2
    comcom7
    fh2r
    @12
    @3
    @6
    wo
    @7
    @10
    @3
    @11
    @6
    @10
    @1
    @1
    wa
    #
    @2
    wa
    @3
    @1
    @2
    @1
    an32
    @13
    @1
    @2
    @1
    anidm
    ran
    ax-r2
    wvb
    @1
    ancom
    2or
    @3
    @6
    ax-a2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
