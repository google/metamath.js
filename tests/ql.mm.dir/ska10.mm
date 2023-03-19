include "wo.mm"
include "wn.mm"
include "wa.mm"
include "oran.mm"
include "con2.mm"
include "bi1.mm"

theorem ska10
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ) ' == ( a ' ^ b ' ) ) = 1

  proof
    wva
    wvb
    wo
    #
    wn
    wva
    wn
    wvb
    wn
    wa
    #
    @0
    @1
    wva
    wvb
    oran
    con2
    bi1
end
