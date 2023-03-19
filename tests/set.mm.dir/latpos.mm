include "clat.mm"
include "wcel.mm"
include "cpo.mm"
include "cjn.mm"
include "cfv.mm"
include "cdm.mm"
include "cbs.mm"
include "cxp.mm"
include "wceq.mm"
include "cmee.mm"
include "wa.mm"
include "eqid.mm"
include "islat.mm"
include "simplbi.mm"

theorem latpos
  let cK: class K


  assert |- ( K e. Lat -> K e. Poset )

  proof
    cK
    clat
    wcel
    cK
    cpo
    wcel
    cK
    cjn
    cfv
    #
    cdm
    cK
    cbs
    cfv
    #
    @1
    cxp
    #
    wceq
    cK
    cmee
    cfv
    #
    cdm
    @2
    wceq
    wa
    @1
    @0
    cK
    @3
    @1
    eqid
    @0
    eqid
    @3
    eqid
    islat
    simplbi
end
