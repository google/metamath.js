include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "com2an.mm"
include "comcom2.mm"
include "com2or.mm"
include "df-i4.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem u4lemc2
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ulemc2.1: |- a C b
  assume ulemc2.2: |- a C c


  assert |- a C ( b ->4 c )

  proof
    wva
    wvb
    wvc
    wa
    #
    wvb
    wn
    #
    wvc
    wa
    #
    wo
    #
    @1
    wvc
    wo
    #
    wvc
    wn
    #
    wa
    #
    wo
    #
    wvb
    wvc
    wi4
    #
    wva
    @3
    @6
    wva
    @0
    @2
    wva
    wvb
    wvc
    ulemc2.1
    ulemc2.2
    com2an
    wva
    @1
    wvc
    wva
    wvb
    ulemc2.1
    comcom2
    #
    ulemc2.2
    com2an
    com2or
    wva
    @4
    @5
    wva
    @1
    wvc
    @9
    ulemc2.2
    com2or
    wva
    wvc
    ulemc2.2
    comcom2
    com2an
    com2or
    @8
    @7
    wvb
    wvc
    df-i4
    ax-r1
    cbtr
end
