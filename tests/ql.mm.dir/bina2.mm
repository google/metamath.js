include "wi3.mm"
include "wn.mm"
include "i3id.mm"
include "ax-a1.mm"
include "ri3.mm"
include "bi1.mm"
include "wwbmp.mm"

theorem bina2
  param wva: term a


  assert |- ( a ' ' ->3 a ) = 1

  proof
    wva
    wva
    wi3
    #
    wva
    wn
    wn
    #
    wva
    wi3
    #
    wva
    i3id
    @0
    @2
    wva
    @1
    wva
    wva
    ax-a1
    ri3
    bi1
    wwbmp
end
