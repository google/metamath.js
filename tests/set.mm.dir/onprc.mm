include "con0.mm"
include "cvv.mm"
include "wcel.mm"
include "word.mm"
include "wn.mm"
include "ordon.mm"
include "ordirr.mm"
include "ax-mp.mm"
include "elong.mm"
include "mpbiri.mm"
include "mto.mm"

theorem onprc



  assert |- -. On e. _V

  proof
    con0
    cvv
    wcel
    #
    con0
    con0
    wcel
    #
    con0
    word
    #
    @1
    wn
    ordon
    con0
    ordirr
    ax-mp
    @0
    @1
    @2
    ordon
    con0
    cvv
    elong
    mpbiri
    mto
end
