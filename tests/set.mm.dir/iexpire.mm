include "ci.mm"
include "ccxp.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "ce.mm"
include "cfv.mm"
include "cr.mm"
include "clog.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "ax-icn.mm"
include "ine0.mm"
include "cxpef.mm"
include "mp3an.mm"
include "logi.mm"
include "oveq2i.mm"
include "halfpire.mm"
include "recni.mm"
include "mulassi.mm"
include "ixi.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "neg1rr.mm"
include "remulcli.mm"
include "reefcl.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem iexpire



  assert |- ( _i ^c _i ) e. RR

  proof
    ci
    ci
    ccxp
    co
    #
    c1
    cneg
    #
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cr
    @0
    ci
    ci
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @4
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    @8
    @0
    @7
    wceq
    ax-icn
    ine0
    ax-icn
    ci
    ci
    cxpef
    mp3an
    @6
    @3
    ce
    @6
    ci
    ci
    @2
    cmul
    co
    #
    cmul
    co
    ci
    ci
    cmul
    co
    #
    @2
    cmul
    co
    @3
    @5
    @9
    ci
    cmul
    logi
    oveq2i
    ci
    ci
    @2
    ax-icn
    ax-icn
    @2
    halfpire
    recni
    mulassi
    @10
    @1
    @2
    cmul
    ixi
    oveq1i
    3eqtr2i
    fveq2i
    eqtri
    @3
    cr
    wcel
    @4
    cr
    wcel
    @1
    @2
    neg1rr
    halfpire
    remulcli
    @3
    reefcl
    ax-mp
    eqeltri
end
