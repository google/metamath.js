include "wo.mm"
include "wa.mm"
include "wn.mm"
include "comcom.mm"
include "df-c2.mm"
include "ancom.mm"
include "2or.mm"
include "ax-r2.mm"
include "or4.mm"
include "fh1.mm"
include "comcom3.mm"
include "ax-r1.mm"
include "df-c1.mm"

theorem com2or
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- a C ( b v c )

  proof
    wvb
    wvc
    wo
    #
    wva
    @0
    wva
    @0
    wva
    wvb
    wa
    #
    wva
    wvc
    wa
    #
    wo
    #
    wva
    wn
    #
    wvb
    wa
    #
    @4
    wvc
    wa
    #
    wo
    #
    wo
    #
    @0
    wva
    wa
    #
    @0
    @4
    wa
    #
    wo
    #
    @0
    @1
    @5
    wo
    #
    @2
    @6
    wo
    #
    wo
    @8
    wvb
    @12
    wvc
    @13
    wvb
    wvb
    wva
    wa
    #
    wvb
    @4
    wa
    #
    wo
    @12
    wvb
    wva
    wva
    wvb
    fh.1
    comcom
    df-c2
    @14
    @1
    @15
    @5
    wvb
    wva
    ancom
    wvb
    @4
    ancom
    2or
    ax-r2
    wvc
    wvc
    wva
    wa
    #
    wvc
    @4
    wa
    #
    wo
    @13
    wvc
    wva
    wva
    wvc
    fh.2
    comcom
    df-c2
    @16
    @2
    @17
    @6
    wvc
    wva
    ancom
    wvc
    @4
    ancom
    2or
    ax-r2
    2or
    @1
    @5
    @2
    @6
    or4
    ax-r2
    @11
    @8
    @9
    @3
    @10
    @7
    @9
    wva
    @0
    wa
    @3
    @0
    wva
    ancom
    wva
    wvb
    wvc
    fh.1
    fh.2
    fh1
    ax-r2
    @10
    @4
    @0
    wa
    @7
    @0
    @4
    ancom
    @4
    wvb
    wvc
    wva
    wvb
    fh.1
    comcom3
    wva
    wvc
    fh.2
    comcom3
    fh1
    ax-r2
    2or
    ax-r1
    ax-r2
    df-c1
    comcom
end
