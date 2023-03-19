include "ccbn.mm"
include "wcel.mm"
include "cnv.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cims.mm"
include "cfv.mm"
include "cc.mm"
include "cms.mm"
include "cnnv.mm"
include "cmin.mm"
include "ccom.mm"
include "eqid.mm"
include "cnims.mm"
include "eqcomi.mm"
include "cncmet.mm"
include "cnnvba.mm"
include "fveq2i.mm"
include "iscbn.mm"
include "mpbir2an.mm"

theorem cnbn
  let cU: class U
  assume cnbn.6: |- U = <. <. + , x. >. , abs >.


  assert |- U e. CBan

  proof
    cU
    ccbn
    wcel
    cU
    cnv
    wcel
    caddc
    cmul
    cop
    cabs
    cop
    #
    cims
    cfv
    #
    cc
    cms
    cfv
    wcel
    cU
    cnbn.6
    cnnv
    @1
    cabs
    cmin
    ccom
    #
    @1
    @2
    @0
    @0
    eqid
    @2
    eqid
    cnims
    eqcomi
    cncmet
    @1
    cU
    cc
    cU
    cnbn.6
    cnnvba
    cU
    cims
    cfv
    @1
    cU
    @0
    cims
    cnbn.6
    fveq2i
    eqcomi
    iscbn
    mpbir2an
end
