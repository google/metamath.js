include "word.mm"
include "con0.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "ordsson.mm"
include "ordtr.mm"
include "jca.mm"
include "cep.mm"
include "wwe.mm"
include "epweon.mm"
include "wess.mm"
include "mpi.mm"
include "df-ord.mm"
include "biimpri.mm"
include "ancoms.mm"
include "sylan.mm"
include "impbii.mm"

theorem dford5
  let cA: class A


  assert |- ( Ord A <-> ( A C_ On /\ Tr A ) )

  proof
    cA
    word
    #
    cA
    con0
    wss
    #
    cA
    wtr
    #
    wa
    @0
    @1
    @2
    cA
    ordsson
    cA
    ordtr
    jca
    @1
    cA
    cep
    wwe
    #
    @2
    @0
    @1
    con0
    cep
    wwe
    @3
    epweon
    cA
    con0
    cep
    wess
    mpi
    @2
    @3
    @0
    @0
    @2
    @3
    wa
    cA
    df-ord
    biimpri
    ancoms
    sylan
    impbii
end
