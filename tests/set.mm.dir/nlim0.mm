include "c0.mm"
include "wlim.mm"
include "word.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "noel.mm"
include "simp2.mm"
include "mto.mm"
include "dflim2.mm"
include "mtbir.mm"

theorem nlim0



  assert |- -. Lim (/)

  proof
    c0
    wlim
    c0
    word
    #
    c0
    c0
    wcel
    #
    c0
    c0
    cuni
    wceq
    #
    w3a
    #
    @3
    @1
    c0
    noel
    @0
    @1
    @2
    simp2
    mto
    c0
    dflim2
    mtbir
end
