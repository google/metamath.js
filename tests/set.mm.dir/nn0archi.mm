include "crefld.mm"
include "cn0.mm"
include "cress.mm"
include "co.mm"
include "ccnfld.mm"
include "carchi.mm"
include "cr.mm"
include "df-refld.mm"
include "oveq1i.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "nn0ssre.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtri.mm"
include "ctos.mm"
include "wa.mm"
include "csubmnd.mm"
include "retos.mm"
include "rearchi.mm"
include "pm3.2i.mm"
include "nn0subm.mm"
include "wb.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "subgsubm.mm"
include "mp2b.mm"
include "subsubm.mm"
include "ax-mp.mm"
include "mpbir2an.mm"
include "submarchi.mm"
include "eqeltrri.mm"

theorem nn0archi



  assert |- ( CCfld |`s NN0 ) e. Archi

  proof
    crefld
    cn0
    cress
    co
    #
    ccnfld
    cn0
    cress
    co
    #
    carchi
    @0
    ccnfld
    cr
    cress
    co
    #
    cn0
    cress
    co
    #
    @1
    crefld
    @2
    cn0
    cress
    df-refld
    oveq1i
    cr
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    cn0
    cr
    wss
    #
    @3
    @1
    wceq
    @5
    crefld
    cdr
    wcel
    resubdrg
    simpli
    #
    nn0ssre
    cr
    cn0
    ccnfld
    @4
    ressabs
    mp2an
    eqtri
    crefld
    ctos
    wcel
    #
    crefld
    carchi
    wcel
    #
    wa
    cn0
    crefld
    csubmnd
    cfv
    wcel
    #
    @0
    carchi
    wcel
    @8
    @9
    retos
    rearchi
    pm3.2i
    @10
    cn0
    ccnfld
    csubmnd
    cfv
    #
    wcel
    #
    @6
    nn0subm
    nn0ssre
    cr
    @11
    wcel
    #
    @10
    @12
    @6
    wa
    wb
    @5
    cr
    ccnfld
    csubg
    cfv
    wcel
    @13
    @7
    cr
    ccnfld
    subrgsubg
    cr
    ccnfld
    subgsubm
    mp2b
    cn0
    cr
    ccnfld
    crefld
    df-refld
    subsubm
    ax-mp
    mpbir2an
    cn0
    crefld
    submarchi
    mp2an
    eqeltrri
end
