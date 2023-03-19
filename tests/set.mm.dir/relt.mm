include "clt.mm"
include "cle.mm"
include "cid.mm"
include "cdif.mm"
include "crefld.mm"
include "cplt.mm"
include "cfv.mm"
include "dflt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ccnfld.mm"
include "cr.mm"
include "cress.mm"
include "co.mm"
include "df-refld.mm"
include "ovex.mm"
include "eqeltri.mm"
include "rele2.mm"
include "eqid.mm"
include "pltfval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem relt



  assert |- < = ( lt ` RRfld )

  proof
    clt
    cle
    cid
    cdif
    #
    crefld
    cplt
    cfv
    #
    dflt2
    crefld
    cvv
    wcel
    @1
    @0
    wceq
    crefld
    ccnfld
    cr
    cress
    co
    cvv
    df-refld
    ccnfld
    cr
    cress
    ovex
    eqeltri
    cvv
    @1
    crefld
    cle
    rele2
    @1
    eqid
    pltfval
    ax-mp
    eqtr4i
end
