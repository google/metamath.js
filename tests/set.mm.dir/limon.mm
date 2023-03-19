include "con0.mm"
include "wlim.mm"
include "word.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wceq.mm"
include "ordon.mm"
include "onn0.mm"
include "unon.mm"
include "eqcomi.mm"
include "df-lim.mm"
include "mpbir3an.mm"

theorem limon



  assert |- Lim On

  proof
    con0
    wlim
    con0
    word
    con0
    c0
    wne
    con0
    con0
    cuni
    #
    wceq
    ordon
    onn0
    @0
    con0
    unon
    eqcomi
    con0
    df-lim
    mpbir3an
end
