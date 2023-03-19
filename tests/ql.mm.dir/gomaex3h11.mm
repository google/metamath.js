include "wo.mm"
include "wn.mm"
include "leor.mm"
include "lecon.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h11
  let wve: term e
  let wvf: term f
  let wvy: term y
  let wvz: term z
  assume gomaex3h11.22: |- y = ( e v f ) '
  assume gomaex3h11.23: |- z = f


  assert |- y =< z '

  proof
    wve
    wvf
    wo
    #
    wn
    wvf
    wn
    wvy
    wvz
    wn
    wvf
    @0
    wvf
    wve
    leor
    lecon
    gomaex3h11.22
    wvz
    wvf
    gomaex3h11.23
    ax-r4
    le3tr1
end
