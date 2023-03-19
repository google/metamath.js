include "wn.mm"
include "lecon.mm"
include "lecon2.mm"
include "lecon1.mm"

theorem lecon3
  param wva: term a
  param wvb: term b
  assume lecon3.1: |- a =< b '


  assert |- b =< a '

  proof
    wva
    wn
    #
    wvb
    wvb
    wn
    #
    @0
    wva
    @1
    lecon3.1
    lecon
    lecon2
    lecon1
end
