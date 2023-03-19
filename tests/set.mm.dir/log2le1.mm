include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "c5.mm"
include "cdc.mm"
include "c3.mm"
include "c6.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "log2ub.mm"
include "2nn0.mm"
include "5nn0.mm"
include "deccl.mm"
include "3nn0.mm"
include "6nn0.mm"
include "3lt10.mm"
include "5lt10.mm"
include "2lt3.mm"
include "decltc.mm"
include "nn0rei.mm"
include "cc0.mm"
include "6nn.mm"
include "decnncl.mm"
include "0nn0.mm"
include "10pos.mm"
include "declti.mm"
include "ltdiv1ii.mm"
include "mpbi.mm"
include "recni.mm"
include "0re.mm"
include "gtneii.mm"
include "dividi.mm"
include "breqtri.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "redivcli.mm"
include "1re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem log2le1



  assert |- ( log ` 2 ) < 1

  proof
    c2
    clog
    cfv
    #
    c2
    c5
    cdc
    #
    c3
    cdc
    #
    c3
    c6
    cdc
    #
    c5
    cdc
    #
    cdiv
    co
    #
    clt
    wbr
    @5
    c1
    clt
    wbr
    @0
    c1
    clt
    wbr
    log2ub
    @5
    @4
    @4
    cdiv
    co
    #
    c1
    clt
    @2
    @4
    clt
    wbr
    @5
    @6
    clt
    wbr
    @1
    @3
    c3
    c5
    c2
    c5
    2nn0
    5nn0
    deccl
    #
    c3
    c6
    3nn0
    6nn0
    deccl
    #
    3nn0
    5nn0
    3lt10
    c2
    c3
    c5
    c6
    2nn0
    3nn0
    5nn0
    6nn0
    5lt10
    2lt3
    decltc
    decltc
    @2
    @4
    @4
    @2
    @1
    c3
    @7
    3nn0
    deccl
    nn0rei
    #
    @4
    @3
    c5
    @8
    5nn0
    deccl
    nn0rei
    #
    @10
    @3
    c5
    cc0
    c3
    c6
    3nn0
    6nn
    decnncl
    5nn0
    0nn0
    10pos
    declti
    #
    ltdiv1ii
    mpbi
    @4
    @4
    @10
    recni
    cc0
    @4
    0re
    @11
    gtneii
    #
    dividi
    breqtri
    @0
    @5
    c1
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
    @2
    @4
    @9
    @10
    @12
    redivcli
    1re
    lttri
    mp2an
end
