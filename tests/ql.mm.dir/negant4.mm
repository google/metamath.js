include "wn.mm"
include "wi4.mm"
include "sac.mm"
include "negantlem10.mm"
include "wi1.mm"
include "ax-r1.mm"
include "lebi.mm"

theorem negant4
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ' ->4 c ) = ( b ' ->4 c )

  proof
    wva
    wn
    #
    wvc
    wi4
    wvb
    wn
    #
    wvc
    wi4
    @0
    @1
    wvc
    wva
    wvb
    wvc
    negant.1
    sac
    #
    negantlem10
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
    negantlem10
    lebi
end
