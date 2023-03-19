include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "eqid.mm"
include "isclm.mm"
include "simp1bi.mm"

theorem clmlmod
  let cW: class W


  assert |- ( W e. CMod -> W e. LMod )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cW
    csca
    cfv
    #
    ccnfld
    @0
    cbs
    cfv
    #
    cress
    co
    wceq
    @1
    ccnfld
    csubrg
    cfv
    wcel
    @0
    @1
    cW
    @0
    eqid
    @1
    eqid
    isclm
    simp1bi
end
