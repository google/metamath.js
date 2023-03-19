include "wi1.mm"
include "wn.mm"
include "ud1lem0b.mm"
include "u1lem12.mm"
include "3tr2.mm"

theorem sac
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume sac.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ' ->1 c ) = ( b ' ->1 c )

  proof
    wva
    wvc
    wi1
    #
    wvc
    wi1
    wvb
    wvc
    wi1
    #
    wvc
    wi1
    wva
    wn
    wvc
    wi1
    wvb
    wn
    wvc
    wi1
    @0
    @1
    wvc
    sac.1
    ud1lem0b
    wva
    wvc
    u1lem12
    wvb
    wvc
    u1lem12
    3tr2
end
