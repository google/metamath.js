include "cid.mm"
include "cres.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wfn.mm"
include "wrel.mm"
include "wss.mm"
include "fnresi.mm"
include "fnrel.mm"
include "relssdmrn.mm"
include "mp2b.mm"
include "dmresi.mm"
include "rnresi.mm"
include "xpeq12i.mm"
include "sseqtri.mm"

theorem idssxp
  let cA: class A


  assert |- ( _I |` A ) C_ ( A X. A )

  proof
    cid
    cA
    cres
    #
    @0
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cA
    cA
    cxp
    @0
    cA
    wfn
    @0
    wrel
    @0
    @3
    wss
    cA
    fnresi
    cA
    @0
    fnrel
    @0
    relssdmrn
    mp2b
    @1
    cA
    @2
    cA
    cA
    dmresi
    cA
    rnresi
    xpeq12i
    sseqtri
end
