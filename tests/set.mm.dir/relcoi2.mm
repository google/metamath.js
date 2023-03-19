include "wrel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wss.mm"
include "wceq.mm"
include "dmrnssfld.mm"
include "wa.mm"
include "unss.mm"
include "simpr.mm"
include "sylbir.mm"
include "cores.mm"
include "mp2b.mm"
include "coi2.mm"
include "syl5eq.mm"

theorem relcoi2
  let cR: class R


  assert |- ( Rel R -> ( ( _I |` U. U. R ) o. R ) = R )

  proof
    cR
    wrel
    cid
    cR
    cuni
    cuni
    #
    cres
    cR
    ccom
    #
    cid
    cR
    ccom
    #
    cR
    cR
    cdm
    #
    cR
    crn
    #
    cun
    @0
    wss
    #
    @4
    @0
    wss
    #
    @1
    @2
    wceq
    cR
    dmrnssfld
    @5
    @3
    @0
    wss
    #
    @6
    wa
    @6
    @3
    @4
    @0
    unss
    @7
    @6
    simpr
    sylbir
    cid
    cR
    @0
    cores
    mp2b
    cR
    coi2
    syl5eq
end
