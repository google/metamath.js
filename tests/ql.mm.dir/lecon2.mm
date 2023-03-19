include "wn.mm"
include "ax-a1.mm"
include "lbtr.mm"
include "lecon1.mm"

theorem lecon2
  param wva: term a
  param wvb: term b
  assume lecon2.1: |- a ' =< b


  assert |- b ' =< a

  proof
    wva
    wvb
    wn
    #
    wva
    wn
    wvb
    @0
    wn
    lecon2.1
    wvb
    ax-a1
    lbtr
    lecon1
end
