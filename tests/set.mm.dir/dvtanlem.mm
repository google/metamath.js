include "ccos.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "ccncf.mm"
include "coscn.mm"
include "eqid.mm"
include "cncfcn1.mm"
include "eleqtri.mm"
include "ccld.mm"
include "cha.mm"
include "cnfldhaus.mm"
include "0cn.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "sncld.mm"
include "mp2an.mm"
include "cldopn.mm"
include "ax-mp.mm"
include "cnima.mm"

theorem dvtanlem



  assert |- ( `' cos " ( CC \ { 0 } ) ) e. ( TopOpen ` CCfld )

  proof
    ccos
    ccnfld
    ctopn
    cfv
    #
    @0
    ccn
    co
    #
    wcel
    cc
    cc0
    csn
    #
    cdif
    #
    @0
    wcel
    #
    ccos
    ccnv
    @3
    cima
    @0
    wcel
    ccos
    cc
    cc
    ccncf
    co
    @1
    coscn
    @0
    @0
    eqid
    #
    cncfcn1
    eleqtri
    @2
    @0
    ccld
    cfv
    wcel
    #
    @4
    @0
    cha
    wcel
    cc0
    cc
    wcel
    @6
    @0
    @5
    cnfldhaus
    0cn
    cc0
    @0
    cc
    cc
    @0
    @0
    @5
    cnfldtopon
    toponunii
    #
    sncld
    mp2an
    @2
    @0
    cc
    @7
    cldopn
    ax-mp
    @3
    ccos
    @0
    @0
    cnima
    mp2an
end
