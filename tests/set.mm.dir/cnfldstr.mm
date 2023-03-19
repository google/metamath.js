include "ccnfld.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cop.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "cstv.mm"
include "ccj.mm"
include "csn.mm"
include "cun.mm"
include "cts.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "cunif.mm"
include "cmetu.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cstr.mm"
include "df-cnfld.mm"
include "c4.mm"
include "c9.mm"
include "eqid.mm"
include "srngfn.mm"
include "c2.mm"
include "cc0.mm"
include "9nn.mm"
include "tsetndx.mm"
include "9lt10.mm"
include "10nn.mm"
include "plendx.mm"
include "1nn0.mm"
include "0nn0.mm"
include "2nn.mm"
include "2pos.mm"
include "declt.mm"
include "decnncl.mm"
include "dsndx.mm"
include "strle3.mm"
include "3nn.mm"
include "unifndx.mm"
include "strle1.mm"
include "2nn0.mm"
include "2lt3.mm"
include "strleun.mm"
include "4lt9.mm"
include "eqbrtri.mm"

theorem cnfldstr



  assert |- CCfld Struct <. 1 , ; 1 3 >.

  proof
    ccnfld
    cnx
    cbs
    cfv
    cc
    cop
    cnx
    cplusg
    cfv
    caddc
    cop
    cnx
    cmulr
    cfv
    cmul
    cop
    ctp
    cnx
    cstv
    cfv
    ccj
    cop
    csn
    cun
    #
    cnx
    cts
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    #
    cop
    cnx
    cple
    cfv
    #
    cle
    cop
    cnx
    cds
    cfv
    #
    @2
    cop
    ctp
    #
    cnx
    cunif
    cfv
    #
    @2
    cmetu
    cfv
    #
    cop
    csn
    #
    cun
    #
    cun
    c1
    c1
    c3
    cdc
    #
    cop
    cstr
    df-cnfld
    c1
    c4
    c9
    @11
    @0
    @10
    cc
    caddc
    @0
    cmul
    ccj
    @0
    eqid
    srngfn
    c9
    c1
    c2
    cdc
    #
    @11
    @11
    @6
    @9
    @1
    @4
    @5
    c9
    c1
    cc0
    cdc
    @12
    @3
    cle
    @2
    9nn
    tsetndx
    9lt10
    10nn
    plendx
    c1
    cc0
    c2
    1nn0
    0nn0
    2nn
    2pos
    declt
    c1
    c2
    1nn0
    2nn
    decnncl
    dsndx
    strle3
    @7
    @11
    @8
    c1
    c3
    1nn0
    3nn
    decnncl
    unifndx
    strle1
    c1
    c2
    c3
    1nn0
    2nn0
    3nn
    2lt3
    declt
    strleun
    4lt9
    strleun
    eqbrtri
end
