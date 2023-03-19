include "wn.mm"
include "wo.mm"
include "wi0.mm"
include "negantlem7.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "3tr2.mm"
include "df-i0.mm"
include "3tr1.mm"

theorem negant0
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ' ->0 c ) = ( b ' ->0 c )

  proof
    wva
    wn
    #
    wn
    #
    wvc
    wo
    #
    wvb
    wn
    #
    wn
    #
    wvc
    wo
    #
    @0
    wvc
    wi0
    @3
    wvc
    wi0
    wva
    wvc
    wo
    wvb
    wvc
    wo
    @2
    @5
    wva
    wvb
    wvc
    negant.1
    negantlem7
    wva
    @1
    wvc
    wva
    ax-a1
    ax-r5
    wvb
    @4
    wvc
    wvb
    ax-a1
    ax-r5
    3tr2
    @0
    wvc
    df-i0
    @3
    wvc
    df-i0
    3tr1
end
