include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "tb.mm"
include "u2lemc1.mm"
include "comcom3.mm"
include "comanr1.mm"
include "fh2.mm"
include "u2lemanb.mm"
include "u2lemab.mm"
include "ran.mm"
include "anass.mm"
include "ancom.mm"
include "3tr2.mm"
include "2or.mm"
include "ax-a2.mm"
include "3tr.mm"
include "df-i1.mm"
include "lan.mm"
include "dfb.mm"
include "3tr1.mm"

theorem u21lembi
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ^ ( b ->1 a ) ) = ( a == b )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wn
    #
    wvb
    wva
    wa
    #
    wo
    #
    wa
    #
    wva
    wvb
    wa
    #
    wva
    wn
    @1
    wa
    #
    wo
    #
    @0
    wvb
    wva
    wi1
    #
    wa
    wva
    wvb
    tb
    @4
    @0
    @1
    wa
    #
    @0
    @2
    wa
    #
    wo
    @6
    @5
    wo
    @7
    @1
    @0
    @2
    wvb
    @0
    wva
    wvb
    u2lemc1
    comcom3
    wvb
    @2
    wvb
    wva
    comanr1
    comcom3
    fh2
    @9
    @6
    @10
    @5
    wva
    wvb
    u2lemanb
    @0
    wvb
    wa
    #
    wva
    wa
    @2
    @10
    @5
    @11
    wvb
    wva
    wva
    wvb
    u2lemab
    ran
    @0
    wvb
    wva
    anass
    wvb
    wva
    ancom
    3tr2
    2or
    @6
    @5
    ax-a2
    3tr
    @8
    @3
    @0
    wvb
    wva
    df-i1
    lan
    wva
    wvb
    dfb
    3tr1
end
