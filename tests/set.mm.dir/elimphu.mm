include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "ccphlo.mm"
include "eqid.mm"
include "cncph.mm"
include "elimel.mm"

theorem elimphu
  let cU: class U


  assert |- if ( U e. CPreHilOLD , U , <. <. + , x. >. , abs >. ) e. CPreHilOLD

  proof
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    ccphlo
    @0
    @0
    eqid
    cncph
    elimel
end
