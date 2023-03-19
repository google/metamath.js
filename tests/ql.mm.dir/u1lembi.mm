include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "tb.mm"
include "ax-a2.mm"
include "2an.mm"
include "coman1.mm"
include "comcom2.mm"
include "coman2.mm"
include "fh3.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "df-i1.mm"
include "ancom.mm"
include "lor.mm"
include "dfb.mm"
include "3tr1.mm"

theorem u1lembi
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->1 b ) ^ ( b ->1 a ) ) = ( a == b )

  proof
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wvb
    wn
    #
    @1
    wo
    #
    wa
    #
    @1
    @0
    @3
    wa
    wo
    #
    wva
    wvb
    wi1
    #
    wvb
    wva
    wi1
    #
    wa
    wva
    wvb
    tb
    @5
    @1
    @0
    wo
    #
    @1
    @3
    wo
    #
    wa
    #
    @6
    @2
    @9
    @4
    @10
    @0
    @1
    ax-a2
    @3
    @1
    ax-a2
    2an
    @6
    @11
    @1
    @0
    @3
    @1
    wva
    wva
    wvb
    coman1
    comcom2
    @1
    wvb
    wva
    wvb
    coman2
    comcom2
    fh3
    ax-r1
    ax-r2
    @7
    @2
    @8
    @4
    wva
    wvb
    df-i1
    @8
    @3
    wvb
    wva
    wa
    #
    wo
    @4
    wvb
    wva
    df-i1
    @12
    @1
    @3
    wvb
    wva
    ancom
    lor
    ax-r2
    2an
    wva
    wvb
    dfb
    3tr1
end
