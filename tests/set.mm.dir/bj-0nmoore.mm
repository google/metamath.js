include "c0.mm"
include "cmoore.mm"
include "wcel.mm"
include "cuni.mm"
include "noel.mm"
include "bj-ismoored0.mm"
include "mto.mm"

theorem bj-0nmoore



  assert |- -. (/) e. Moore_

  proof
    c0
    cmoore
    wcel
    c0
    cuni
    #
    c0
    wcel
    @0
    noel
    c0
    bj-ismoored0
    mto
end
