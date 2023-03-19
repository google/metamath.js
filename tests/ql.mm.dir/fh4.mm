include "wa.mm"
include "wo.mm"
include "wn.mm"
include "comcom4.mm"
include "fh2.mm"
include "anor2.mm"
include "df-a.mm"
include "ax-r1.mm"
include "lor.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "oran.mm"
include "2an.mm"
include "3tr2.mm"
include "con1.mm"

theorem fh4
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( b v ( a ^ c ) ) = ( ( b v a ) ^ ( b v c ) )

  proof
    wvb
    wva
    wvc
    wa
    #
    wo
    #
    wvb
    wva
    wo
    #
    wvb
    wvc
    wo
    #
    wa
    #
    wvb
    wn
    #
    wva
    wn
    #
    wvc
    wn
    #
    wo
    #
    wa
    #
    @5
    @6
    wa
    #
    @5
    @7
    wa
    #
    wo
    #
    @1
    wn
    #
    @4
    wn
    #
    @6
    @5
    @7
    wva
    wvb
    fh.1
    comcom4
    wva
    wvc
    fh.2
    comcom4
    fh2
    @9
    wvb
    @8
    wn
    #
    wo
    #
    wn
    @13
    wvb
    @8
    anor2
    @16
    @1
    @15
    @0
    wvb
    @0
    @15
    wva
    wvc
    df-a
    ax-r1
    lor
    ax-r4
    ax-r2
    @12
    @10
    wn
    #
    @11
    wn
    #
    wa
    #
    wn
    @14
    @10
    @11
    oran
    @19
    @4
    @4
    @19
    @2
    @17
    @3
    @18
    wvb
    wva
    oran
    wvb
    wvc
    oran
    2an
    ax-r1
    ax-r4
    ax-r2
    3tr2
    con1
end
