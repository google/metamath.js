include "ctop.mm"
include "chmph.mm"
include "chmeo.mm"
include "ccnv.mm"
include "cvv.mm"
include "c1o.mm"
include "cdif.mm"
include "cima.mm"
include "cxp.mm"
include "df-hmph.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "wceq.mm"
include "hmeofn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "brel.mm"

theorem hmphtop
  let cJ: class J
  let cK: class K


  assert |- ( J ~= K -> ( J e. Top /\ K e. Top ) )

  proof
    cJ
    cK
    ctop
    ctop
    chmph
    chmph
    chmeo
    ccnv
    cvv
    c1o
    cdif
    #
    cima
    #
    ctop
    ctop
    cxp
    #
    df-hmph
    @1
    chmeo
    cdm
    #
    @2
    chmeo
    @0
    cnvimass
    chmeo
    @2
    wfn
    @3
    @2
    wceq
    hmeofn
    @2
    chmeo
    fndm
    ax-mp
    sseqtri
    eqsstri
    brel
end
