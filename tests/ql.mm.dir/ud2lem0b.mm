include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "ax-r4.mm"
include "ran.mm"
include "lor.mm"
include "df-i2.mm"
include "3tr1.mm"

theorem ud2lem0b
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume ud2lem0a.1: |- a = b


  assert |- ( a ->2 c ) = ( b ->2 c )

  proof
    wvc
    wva
    wn
    #
    wvc
    wn
    #
    wa
    #
    wo
    wvc
    wvb
    wn
    #
    @1
    wa
    #
    wo
    wva
    wvc
    wi2
    wvb
    wvc
    wi2
    @2
    @4
    wvc
    @0
    @3
    @1
    wva
    wvb
    ud2lem0a.1
    ax-r4
    ran
    lor
    wva
    wvc
    df-i2
    wvb
    wvc
    df-i2
    3tr1
end
