include "csur.mm"
include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "onprc.mm"
include "cbday.mm"
include "wfo.mm"
include "bdayfo.mm"
include "fornex.mm"
include "mpi.mm"
include "mto.mm"

theorem noprc



  assert |- -. No e. _V

  proof
    csur
    cvv
    wcel
    #
    con0
    cvv
    wcel
    #
    onprc
    @0
    csur
    con0
    cbday
    wfo
    @1
    bdayfo
    csur
    con0
    cvv
    cbday
    fornex
    mpi
    mto
end
