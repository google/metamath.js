include "wfun.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "wss.mm"
include "crn.mm"
include "cres.mm"
include "wceq.mm"
include "wrel.mm"
include "df-fun.mm"
include "simprbi.mm"
include "cdm.mm"
include "iss.mm"
include "dfdm4.mm"
include "dmcoeq.mm"
include "ax-mp.mm"
include "df-rn.mm"
include "eqtr4i.mm"
include "reseq2i.mm"
include "eqeq2i.mm"
include "bitri.mm"
include "sylib.mm"

theorem funcocnv2
  let cF: class F


  assert |- ( Fun F -> ( F o. `' F ) = ( _I |` ran F ) )

  proof
    cF
    wfun
    #
    cF
    cF
    ccnv
    #
    ccom
    #
    cid
    wss
    #
    @2
    cid
    cF
    crn
    #
    cres
    #
    wceq
    #
    @0
    cF
    wrel
    @3
    cF
    df-fun
    simprbi
    @3
    @2
    cid
    @2
    cdm
    #
    cres
    #
    wceq
    @6
    @2
    iss
    @8
    @5
    @2
    @7
    @4
    cid
    @7
    @1
    cdm
    #
    @4
    cF
    cdm
    @1
    crn
    wceq
    @7
    @9
    wceq
    cF
    dfdm4
    cF
    @1
    dmcoeq
    ax-mp
    cF
    df-rn
    eqtr4i
    reseq2i
    eqeq2i
    bitri
    sylib
end
