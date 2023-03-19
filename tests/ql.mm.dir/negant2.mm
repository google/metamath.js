include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "negantlem6.mm"
include "ax-a1.mm"
include "ran.mm"
include "3tr2.mm"
include "lor.mm"
include "df-i2.mm"
include "3tr1.mm"

theorem negant2
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ' ->2 c ) = ( b ' ->2 c )

  proof
    wvc
    wva
    wn
    #
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
    wn
    #
    @2
    wa
    #
    wo
    @0
    wvc
    wi2
    @4
    wvc
    wi2
    @3
    @6
    wvc
    wva
    @2
    wa
    wvb
    @2
    wa
    @3
    @6
    wva
    wvb
    wvc
    negant.1
    negantlem6
    wva
    @1
    @2
    wva
    ax-a1
    ran
    wvb
    @5
    @2
    wvb
    ax-a1
    ran
    3tr2
    lor
    @0
    wvc
    df-i2
    @4
    wvc
    df-i2
    3tr1
end
