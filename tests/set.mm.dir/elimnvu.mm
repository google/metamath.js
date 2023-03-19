include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cnv.mm"
include "eqid.mm"
include "cnnv.mm"
include "elimel.mm"

theorem elimnvu
  let cU: class U


  assert |- if ( U e. NrmCVec , U , <. <. + , x. >. , abs >. ) e. NrmCVec

  proof
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cnv
    @0
    @0
    eqid
    cnnv
    elimel
end
