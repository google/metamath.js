include "cabs.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccn.mm"
include "co.mm"
include "cc.mm"
include "cr.mm"
include "ccncf.mm"
include "eqid.mm"
include "abscn.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "ax-resscn.mm"
include "crest.mm"
include "ctopon.mm"
include "wcel.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "tgioo2.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "eleqtrri.mm"

theorem abscncfALT



  assert |- abs e. ( CC -cn-> RR )

  proof
    cabs
    ccnfld
    ctopn
    cfv
    #
    cioo
    crn
    ctg
    cfv
    #
    ccn
    co
    #
    cc
    cr
    ccncf
    co
    #
    @0
    @1
    @0
    eqid
    #
    @1
    eqid
    abscn
    cc
    cc
    wss
    cr
    cc
    wss
    @3
    @2
    wceq
    cc
    ssid
    ax-resscn
    cc
    cr
    @0
    @0
    @1
    @4
    @0
    cc
    crest
    co
    #
    @0
    @0
    cc
    ctopon
    cfv
    #
    wcel
    @5
    @0
    wceq
    @0
    @4
    cnfldtopon
    #
    @0
    @6
    cc
    cc
    @0
    @7
    toponunii
    restid
    ax-mp
    eqcomi
    @0
    @4
    tgioo2
    cncfcn
    mp2an
    eleqtrri
end
