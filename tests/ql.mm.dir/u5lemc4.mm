include "wi5.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-i5.mm"
include "comid.mm"
include "comcom2.mm"
include "fh2r.mm"
include "ax-r1.mm"
include "ancom.mm"
include "wt.mm"
include "df-t.mm"
include "lan.mm"
include "an1.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "comcom3.mm"
include "comcom4.mm"
include "fh4.mm"
include "ax-a2.mm"
include "2an.mm"

theorem u5lemc4
  let wva: term a
  let wvb: term b
  assume ulemc3.1: |- a C b


  assert |- ( a ->5 b ) = ( a ' v b )

  proof
    wva
    wvb
    wi5
    wva
    wvb
    wa
    wva
    wn
    #
    wvb
    wa
    wo
    #
    @0
    wvb
    wn
    #
    wa
    #
    wo
    #
    @0
    wvb
    wo
    #
    wva
    wvb
    df-i5
    @4
    wvb
    @3
    wo
    #
    @5
    @1
    wvb
    @3
    @1
    wva
    @0
    wo
    #
    wvb
    wa
    #
    wvb
    @8
    @1
    wva
    wvb
    @0
    ulemc3.1
    wva
    wva
    wva
    comid
    comcom2
    fh2r
    ax-r1
    @8
    wvb
    @7
    wa
    #
    wvb
    @7
    wvb
    ancom
    @9
    wvb
    wt
    wa
    wvb
    @7
    wt
    wvb
    wt
    @7
    wva
    df-t
    ax-r1
    lan
    wvb
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r5
    @6
    wvb
    @0
    wo
    #
    wvb
    @2
    wo
    #
    wa
    #
    @5
    @0
    wvb
    @2
    wva
    wvb
    ulemc3.1
    comcom3
    wva
    wvb
    ulemc3.1
    comcom4
    fh4
    @12
    @5
    wt
    wa
    @5
    @10
    @5
    @11
    wt
    wvb
    @0
    ax-a2
    wt
    @11
    wvb
    df-t
    ax-r1
    2an
    @5
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
