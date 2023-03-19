include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cims.mm"
include "cfv.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnnv.mm"
include "cnnvm.mm"
include "cnnvnm.mm"
include "eqid.mm"
include "imsval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem cnims
  let cD: class D
  let cU: class U
  assume cnims.6: |- U = <. <. + , x. >. , abs >.
  assume cnims.7: |- D = ( abs o. - )


  assert |- D = ( IndMet ` U )

  proof
    cD
    cabs
    cmin
    ccom
    #
    cU
    cims
    cfv
    #
    cnims.7
    cU
    cnv
    wcel
    @1
    @0
    wceq
    cU
    cnims.6
    cnnv
    @1
    cU
    cmin
    cabs
    cU
    cnims.6
    cnnvm
    cU
    cnims.6
    cnnvnm
    @1
    eqid
    imsval
    ax-mp
    eqtr4i
end
