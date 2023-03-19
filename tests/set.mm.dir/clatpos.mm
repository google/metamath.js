include "ccla.mm"
include "wcel.mm"
include "cpo.mm"
include "club.mm"
include "cfv.mm"
include "cdm.mm"
include "cbs.mm"
include "cpw.mm"
include "wceq.mm"
include "cglb.mm"
include "wa.mm"
include "eqid.mm"
include "isclat.mm"
include "simplbi.mm"

theorem clatpos
  let cK: class K


  assert |- ( K e. CLat -> K e. Poset )

  proof
    cK
    ccla
    wcel
    cK
    cpo
    wcel
    cK
    club
    cfv
    #
    cdm
    cK
    cbs
    cfv
    #
    cpw
    #
    wceq
    cK
    cglb
    cfv
    #
    cdm
    @2
    wceq
    wa
    @1
    @0
    @3
    cK
    @1
    eqid
    @0
    eqid
    @3
    eqid
    isclat
    simplbi
end
