include "wa.mm"
include "ancom.mm"
include "lea.mm"
include "bltr.mm"

theorem lear
  param wva: term a
  param wvb: term b


  assert |- ( a ^ b ) =< b

  proof
    wva
    wvb
    wa
    wvb
    wva
    wa
    wvb
    wva
    wvb
    ancom
    wvb
    wva
    lea
    bltr
end
