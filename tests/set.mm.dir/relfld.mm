include "wrel.mm"
include "cuni.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cxp.mm"
include "wss.mm"
include "relssdmrn.mm"
include "uniss.mm"
include "3syl.mm"
include "unixpss.mm"
include "syl6ss.mm"
include "dmrnssfld.mm"
include "a1i.mm"
include "eqssd.mm"

theorem relfld
  let cR: class R


  assert |- ( Rel R -> U. U. R = ( dom R u. ran R ) )

  proof
    cR
    wrel
    #
    cR
    cuni
    #
    cuni
    #
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    @0
    @2
    @3
    @4
    cxp
    #
    cuni
    #
    cuni
    #
    @5
    @0
    cR
    @6
    wss
    @1
    @7
    wss
    @2
    @8
    wss
    cR
    relssdmrn
    cR
    @6
    uniss
    @1
    @7
    uniss
    3syl
    @3
    @4
    unixpss
    syl6ss
    @5
    @2
    wss
    @0
    cR
    dmrnssfld
    a1i
    eqssd
end
