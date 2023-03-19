include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i2.mm"
include "u2lemc1.mm"
include "comcom3.mm"
include "comcom4.mm"
include "fh4.mm"
include "u2lemonb.mm"
include "df-t.mm"
include "ax-r1.mm"
include "2an.mm"
include "an1.mm"
include "ax-r2.mm"

theorem u2lem3
  param wva: term a
  param wvb: term b


  assert |- ( a ->2 ( b ->2 a ) ) = 1

  proof
    wva
    wvb
    wva
    wi2
    #
    wi2
    @0
    wva
    wn
    #
    @0
    wn
    #
    wa
    wo
    #
    wt
    wva
    @0
    df-i2
    @3
    @0
    @1
    wo
    #
    @0
    @2
    wo
    #
    wa
    #
    wt
    @1
    @0
    @2
    wva
    @0
    wvb
    wva
    u2lemc1
    #
    comcom3
    wva
    @0
    @7
    comcom4
    fh4
    @6
    wt
    wt
    wa
    wt
    @4
    wt
    @5
    wt
    wvb
    wva
    u2lemonb
    wt
    @5
    @0
    df-t
    ax-r1
    2an
    wt
    an1
    ax-r2
    ax-r2
    ax-r2
end
