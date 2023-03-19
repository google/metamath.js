include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "leo.mm"
include "df-i1.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lbtr.mm"
include "lecom.mm"
include "comcom6.mm"

theorem negantlem1
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- a C ( b ->1 c )

  proof
    wva
    wvb
    wvc
    wi1
    #
    wva
    wn
    #
    @0
    @1
    @1
    wva
    wvc
    wa
    #
    wo
    #
    @0
    @1
    @2
    leo
    @3
    wva
    wvc
    wi1
    #
    @0
    @4
    @3
    wva
    wvc
    df-i1
    ax-r1
    negant.1
    ax-r2
    lbtr
    lecom
    comcom6
end
