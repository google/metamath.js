include "wa.mm"
include "i3ran.mm"
include "ancom.mm"
include "i33tr1.mm"

theorem i3lan
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume i3lan.1: |- ( a ->3 b ) = 1


  assert |- ( ( c ^ a ) ->3 ( c ^ b ) ) = 1

  proof
    wva
    wvc
    wa
    wvb
    wvc
    wa
    wvc
    wva
    wa
    wvc
    wvb
    wa
    wva
    wvb
    wvc
    i3lan.1
    i3ran
    wvc
    wva
    ancom
    wvc
    wvb
    ancom
    i33tr1
end
