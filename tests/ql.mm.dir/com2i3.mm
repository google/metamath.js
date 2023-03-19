include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "comcom2.mm"
include "com2an.mm"
include "com2or.mm"
include "df-i3.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem com2i3
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume com2i3.1: |- a C b
  assume com2i3.2: |- a C c


  assert |- a C ( b ->3 c )

  proof
    wva
    wvb
    wn
    #
    wvc
    wa
    #
    @0
    wvc
    wn
    #
    wa
    #
    wo
    #
    wvb
    @0
    wvc
    wo
    #
    wa
    #
    wo
    #
    wvb
    wvc
    wi3
    #
    wva
    @4
    @6
    wva
    @1
    @3
    wva
    @0
    wvc
    wva
    wvb
    com2i3.1
    comcom2
    #
    com2i3.2
    com2an
    wva
    @0
    @2
    @9
    wva
    wvc
    com2i3.2
    comcom2
    com2an
    com2or
    wva
    wvb
    @5
    com2i3.1
    wva
    @0
    wvc
    @9
    com2i3.2
    com2or
    com2an
    com2or
    @8
    @7
    wvb
    wvc
    df-i3
    ax-r1
    cbtr
end
