include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "ran.mm"
include "u1lemanb.mm"
include "3tr2.mm"

theorem negantlem5
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ' ^ c ' ) = ( b ' ^ c ' )

  proof
    wva
    wvc
    wi1
    #
    wvc
    wn
    #
    wa
    wvb
    wvc
    wi1
    #
    @1
    wa
    wva
    wn
    @1
    wa
    wvb
    wn
    @1
    wa
    @0
    @2
    @1
    negant.1
    ran
    wva
    wvc
    u1lemanb
    wvb
    wvc
    u1lemanb
    3tr2
end
