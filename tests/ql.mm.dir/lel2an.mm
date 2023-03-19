include "wa.mm"
include "le2an.mm"
include "anidm.mm"
include "lbtr.mm"

theorem lel2an
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume lel2.1: |- a =< b
  assume lel2.2: |- c =< b


  assert |- ( a ^ c ) =< b

  proof
    wva
    wvc
    wa
    wvb
    wvb
    wa
    wvb
    wva
    wvb
    wvc
    wvb
    lel2.1
    lel2.2
    le2an
    wvb
    anidm
    lbtr
end
