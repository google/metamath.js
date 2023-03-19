include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "df-i1.mm"
include "comid.mm"
include "comcom3.mm"
include "comor1.mm"
include "fh3.mm"
include "wt.mm"
include "ancom.mm"
include "ax-a2.mm"
include "df-t.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lan.mm"
include "an1.mm"
include "oran.mm"
include "ax-r4.mm"
include "con2.mm"
include "ax-r5.mm"
include "oml.mm"
include "3tr.mm"

theorem ud1lem2
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( a ' ^ b ' ) ) ->1 a ) = ( a v b )

  proof
    wva
    wva
    wn
    #
    wvb
    wn
    wa
    #
    wo
    #
    wva
    wi1
    @2
    wn
    #
    @2
    wva
    wa
    wo
    @3
    @2
    wo
    #
    @3
    wva
    wo
    #
    wa
    #
    wva
    wvb
    wo
    #
    @2
    wva
    df-i1
    @3
    @2
    wva
    @2
    @2
    @2
    comid
    comcom3
    @2
    wva
    wva
    @1
    comor1
    comcom3
    fh3
    @6
    @5
    @4
    wa
    @5
    wt
    wa
    #
    @7
    @4
    @5
    ancom
    @4
    wt
    @5
    @4
    @2
    @3
    wo
    #
    wt
    @3
    @2
    ax-a2
    wt
    @9
    @2
    df-t
    ax-r1
    ax-r2
    lan
    @8
    @5
    @0
    @7
    wa
    #
    wva
    wo
    #
    @7
    @5
    an1
    @3
    @10
    wva
    @2
    @10
    @2
    @0
    @1
    wn
    #
    wa
    #
    wn
    @10
    wn
    wva
    @1
    oran
    @13
    @10
    @12
    @7
    @0
    @7
    @12
    wva
    wvb
    oran
    ax-r1
    lan
    ax-r4
    ax-r2
    con2
    ax-r5
    @11
    wva
    @10
    wo
    @7
    @10
    wva
    ax-a2
    wva
    wvb
    oml
    ax-r2
    3tr
    3tr
    3tr
end
