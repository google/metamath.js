include "cc.mm"
include "wss.mm"
include "ccncf.mm"
include "co.mm"
include "ccn.mm"
include "wceq.mm"
include "ssid.mm"
include "crest.mm"
include "ctop.mm"
include "wcel.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"

theorem cncfcn1
  let cJ: class J
  assume cncfcn1.1: |- J = ( TopOpen ` CCfld )


  assert |- ( CC -cn-> CC ) = ( J Cn J )

  proof
    cc
    cc
    wss
    #
    @0
    cc
    cc
    ccncf
    co
    cJ
    cJ
    ccn
    co
    wceq
    cc
    ssid
    #
    @1
    cc
    cc
    cJ
    cJ
    cJ
    cncfcn1.1
    cJ
    cc
    crest
    co
    #
    cJ
    cJ
    ctop
    wcel
    @2
    cJ
    wceq
    cJ
    cncfcn1.1
    cnfldtop
    cJ
    ctop
    cc
    cc
    cJ
    cJ
    cncfcn1.1
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    #
    @3
    cncfcn
    mp2an
end
