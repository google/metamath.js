include "wn.mm"
include "wi3.mm"
include "sac.mm"
include "negantlem9.mm"
include "wi1.mm"
include "ax-r1.mm"
include "lebi.mm"

theorem negant3
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ' ->3 c ) = ( b ' ->3 c )

  proof
    wva
    wn
    #
    wvc
    wi3
    wvb
    wn
    #
    wvc
    wi3
    @0
    @1
    wvc
    wva
    wvb
    wvc
    negant.1
    sac
    #
    negantlem9
    @1
    @0
    wvc
    @0
    wvc
    wi1
    @1
    wvc
    wi1
    @2
    ax-r1
    negantlem9
    lebi
end
