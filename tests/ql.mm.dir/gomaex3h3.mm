include "wo.mm"
include "wn.mm"
include "leo.mm"
include "ax-a1.mm"
include "lbtr.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h3
  let wvc: term c
  let wvd: term d
  let wvj: term j
  let wvi: term i
  assume gomaex3h3.14: |- i = c
  assume gomaex3h3.15: |- j = ( c v d ) '


  assert |- i =< j '

  proof
    wvc
    wvc
    wvd
    wo
    #
    wn
    #
    wn
    #
    wvi
    wvj
    wn
    wvc
    @0
    @2
    wvc
    wvd
    leo
    @0
    ax-a1
    lbtr
    gomaex3h3.14
    wvj
    @1
    gomaex3h3.15
    ax-r4
    le3tr1
end
