include "wo.mm"
include "wa.mm"
include "anabs.mm"
include "bi1.mm"

theorem wa5c
  param wva: term a
  param wvb: term b


  assert |- ( ( a ^ ( a v b ) ) == a ) = 1

  proof
    wva
    wva
    wvb
    wo
    wa
    wva
    wva
    wvb
    anabs
    bi1
end
