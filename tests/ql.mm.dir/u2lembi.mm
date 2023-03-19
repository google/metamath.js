include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "tb.mm"
include "ancom.mm"
include "coman1.mm"
include "comcom7.mm"
include "coman2.mm"
include "fh3r.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "df-i2.mm"
include "lor.mm"
include "2an.mm"
include "dfb.mm"
include "3tr1.mm"

theorem u2lembi
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->2 b ) ^ ( b ->2 a ) ) = ( a == b )

  proof
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    @2
    wo
    #
    wa
    #
    wva
    wvb
    wa
    @2
    wo
    #
    wva
    wvb
    wi2
    #
    wvb
    wva
    wi2
    #
    wa
    wva
    wvb
    tb
    @5
    @4
    @3
    wa
    #
    @6
    @3
    @4
    ancom
    @6
    @9
    @2
    wva
    wvb
    @2
    wva
    @0
    @1
    coman1
    comcom7
    @2
    wvb
    @0
    @1
    coman2
    comcom7
    fh3r
    ax-r1
    ax-r2
    @7
    @3
    @8
    @4
    wva
    wvb
    df-i2
    @8
    wva
    @1
    @0
    wa
    #
    wo
    @4
    wvb
    wva
    df-i2
    @10
    @2
    wva
    @1
    @0
    ancom
    lor
    ax-r2
    2an
    wva
    wvb
    dfb
    3tr1
end
