include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "df-i2.mm"
include "ud2lem0c.mm"
include "ran.mm"
include "lor.mm"
include "coman2.mm"
include "comcom.mm"
include "comid.mm"
include "comcom2.mm"
include "fh3.mm"
include "wt.mm"
include "ancom.mm"
include "df-t.mm"
include "ax-r1.mm"
include "2an.mm"
include "an1.mm"
include "orabs.mm"
include "ax-r2.mm"

theorem ud2lem3
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ->2 ( a v b ) ) = ( a v b )

  proof
    wva
    wvb
    wi2
    #
    wva
    wvb
    wo
    #
    wi2
    @1
    @0
    wn
    #
    @1
    wn
    #
    wa
    #
    wo
    #
    @1
    @0
    @1
    df-i2
    @5
    @1
    wvb
    wn
    #
    @1
    wa
    #
    @3
    wa
    #
    wo
    #
    @1
    @4
    @8
    @1
    @2
    @7
    @3
    wva
    wvb
    ud2lem0c
    ran
    lor
    @9
    @1
    @7
    wo
    #
    @1
    @3
    wo
    #
    wa
    #
    @1
    @1
    @7
    @3
    @7
    @1
    @6
    @1
    coman2
    comcom
    @1
    @1
    @1
    comid
    comcom2
    fh3
    @12
    @1
    @1
    @6
    wa
    #
    wo
    #
    wt
    wa
    #
    @1
    @10
    @14
    @11
    wt
    @7
    @13
    @1
    @6
    @1
    ancom
    lor
    wt
    @11
    @1
    df-t
    ax-r1
    2an
    @15
    @14
    @1
    @14
    an1
    @1
    @6
    orabs
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
