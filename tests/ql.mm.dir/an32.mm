include "wa.mm"
include "ancom.mm"
include "lan.mm"
include "anass.mm"
include "3tr1.mm"

theorem an32
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ^ b ) ^ c ) = ( ( a ^ c ) ^ b )

  proof
    wva
    wvb
    wvc
    wa
    #
    wa
    wva
    wvc
    wvb
    wa
    #
    wa
    wva
    wvb
    wa
    wvc
    wa
    wva
    wvc
    wa
    wvb
    wa
    @0
    @1
    wva
    wvb
    wvc
    ancom
    lan
    wva
    wvb
    wvc
    anass
    wva
    wvc
    wvb
    anass
    3tr1
end
