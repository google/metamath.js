include "wi3.mm"
include "li3.mm"
include "bi1.mm"
include "wwbmp.mm"

theorem i3btr
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume i3btr.1: |- ( a ->3 b ) = 1
  assume i3btr.2: |- b = c


  assert |- ( a ->3 c ) = 1

  proof
    wva
    wvb
    wi3
    #
    wva
    wvc
    wi3
    #
    i3btr.1
    @0
    @1
    wvb
    wvc
    wva
    i3btr.2
    li3
    bi1
    wwbmp
end
