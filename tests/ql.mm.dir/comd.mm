include "wn.mm"
include "wa.mm"
include "wo.mm"
include "comcom4.mm"
include "df-c2.mm"
include "con3.mm"
include "oran.mm"
include "con2.mm"
include "2an.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem comd
  param wva: term a
  param wvb: term b
  assume comcom.1: |- a C b


  assert |- a = ( ( a v b ) ^ ( a v b ' ) )

  proof
    wva
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    @0
    @1
    wn
    wa
    #
    wo
    #
    wn
    #
    wva
    wvb
    wo
    #
    wva
    @1
    wo
    #
    wa
    #
    wva
    @4
    @0
    @1
    wva
    wvb
    comcom.1
    comcom4
    df-c2
    con3
    @5
    @2
    wn
    #
    @3
    wn
    #
    wa
    #
    @8
    @4
    @11
    @2
    @3
    oran
    con2
    @8
    @11
    @6
    @9
    @7
    @10
    wva
    wvb
    oran
    wva
    @1
    oran
    2an
    ax-r1
    ax-r2
    ax-r2
end
