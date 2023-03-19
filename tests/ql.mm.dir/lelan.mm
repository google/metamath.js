include "wa.mm"
include "leran.mm"
include "ancom.mm"
include "le3tr1.mm"

theorem lelan
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume lel.1: |- a =< b


  assert |- ( c ^ a ) =< ( c ^ b )

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
    lel.1
    leran
    wvc
    wva
    ancom
    wvc
    wvb
    ancom
    le3tr1
end
