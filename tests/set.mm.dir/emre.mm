include "c1.mm"
include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "cr.mm"
include "cem.mm"
include "wcel.mm"
include "wss.mm"
include "1re.mm"
include "crp.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "resubcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "emcl.mm"
include "sselii.mm"

theorem emre



  assert |- gamma e. RR

  proof
    c1
    c2
    clog
    cfv
    #
    cmin
    co
    #
    c1
    cicc
    co
    #
    cr
    cem
    @1
    cr
    wcel
    c1
    cr
    wcel
    @2
    cr
    wss
    c1
    @0
    1re
    c2
    crp
    wcel
    @0
    cr
    wcel
    2rp
    c2
    relogcl
    ax-mp
    resubcli
    1re
    @1
    c1
    iccssre
    mp2an
    emcl
    sselii
end
