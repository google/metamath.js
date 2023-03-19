include "ccph.mm"
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
include "cclm.mm"
include "cphlmod.mm"
include "eqid.mm"
include "cphsca.mm"
include "cphsubrg.mm"
include "isclm.mm"
include "syl3anbrc.mm"

theorem cphclm
  let cW: class W


  assert |- ( W e. CPreHil -> W e. CMod )

  proof
    cW
    ccph
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
    cW
    cclm
    wcel
    cW
    cphlmod
    @0
    @1
    cW
    @0
    eqid
    #
    @1
    eqid
    #
    cphsca
    @0
    @1
    cW
    @2
    @3
    cphsubrg
    @0
    @1
    cW
    @2
    @3
    isclm
    syl3anbrc
end
