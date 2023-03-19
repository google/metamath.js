include "wn.mm"
include "wo.mm"
include "wa.mm"
include "anor1.mm"
include "ax-r1.mm"
include "con3.mm"

theorem oran2
  let wva: term a
  let wvb: term b


  assert |- ( a ' v b ) = ( a ^ b ' ) '

  proof
    wva
    wn
    wvb
    wo
    #
    wva
    wvb
    wn
    wa
    #
    @1
    @0
    wn
    wva
    wvb
    anor1
    ax-r1
    con3
end
