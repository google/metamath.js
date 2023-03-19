include "wa.mm"
include "wo.mm"
include "orabs.mm"
include "bi1.mm"

theorem wa5b
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( a ^ b ) ) == a ) = 1

  proof
    wva
    wva
    wvb
    wa
    wo
    wva
    wva
    wvb
    orabs
    bi1
end
