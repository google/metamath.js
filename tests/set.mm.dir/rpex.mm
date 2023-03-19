include "crp.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "csubg.mm"
include "eqid.mm"
include "rpmsubg.mm"
include "elexi.mm"

theorem rpex



  assert |- RR+ e. _V

  proof
    crp
    ccnfld
    cmgp
    cfv
    cc
    cc0
    csn
    cdif
    cress
    co
    #
    csubg
    cfv
    @0
    @0
    eqid
    rpmsubg
    elexi
end
