include "wn.mm"
include "wo.mm"
include "wa.mm"
include "anor2.mm"
include "ax-r1.mm"
include "con3.mm"

theorem oran1
  param wva: term a
  param wvb: term b


  assert |- ( a v b ' ) = ( a ' ^ b ) '

  proof
    wva
    wvb
    wn
    wo
    #
    wva
    wn
    wvb
    wa
    #
    @1
    @0
    wn
    wva
    wvb
    anor2
    ax-r1
    con3
end
