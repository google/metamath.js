include "cale.mm"
include "crn.mm"
include "cuni.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "alephprc.mm"
include "uniexb.mm"
include "mtbi.mm"
include "elex.mm"
include "mto.mm"
include "word.mm"
include "wo.mm"
include "wss.mm"
include "alephsson.mm"
include "ssorduni.mm"
include "ax-mp.mm"
include "ordeleqon.mm"
include "mpbi.mm"
include "mtpor.mm"

theorem unialeph



  assert |- U. ran aleph = On

  proof
    cale
    crn
    #
    cuni
    #
    con0
    wcel
    #
    @1
    con0
    wceq
    #
    @2
    @1
    cvv
    wcel
    #
    @0
    cvv
    wcel
    @4
    alephprc
    @0
    uniexb
    mtbi
    @1
    con0
    elex
    mto
    @1
    word
    #
    @2
    @3
    wo
    @0
    con0
    wss
    @5
    alephsson
    @0
    ssorduni
    ax-mp
    @1
    ordeleqon
    mpbi
    mtpor
end
