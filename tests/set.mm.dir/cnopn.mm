include "cc.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cuni.mm"
include "unicntop.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "ssid.mm"
include "uniopn.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem cnopn



  assert |- CC e. ( TopOpen ` CCfld )

  proof
    cc
    ccnfld
    ctopn
    cfv
    #
    cuni
    #
    @0
    unicntop
    @0
    ctop
    wcel
    @0
    @0
    wss
    @1
    @0
    wcel
    @0
    @0
    eqid
    cnfldtop
    @0
    ssid
    @0
    @0
    uniopn
    mp2an
    eqeltri
end
