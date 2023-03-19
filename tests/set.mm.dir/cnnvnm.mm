include "cnmcv.mm"
include "cfv.mm"
include "c2nd.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "eqid.mm"
include "nmcvfval.mm"
include "fveq2i.mm"
include "opex.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "absf.mm"
include "cnex.mm"
include "fex.mm"
include "mp2an.mm"
include "op2nd.mm"
include "3eqtrri.mm"

theorem cnnvnm
  let cU: class U
  assume cnnvnm.6: |- U = <. <. + , x. >. , abs >.


  assert |- abs = ( normCV ` U )

  proof
    cU
    cnmcv
    cfv
    #
    cU
    c2nd
    cfv
    caddc
    cmul
    cop
    #
    cabs
    cop
    #
    c2nd
    cfv
    cabs
    cU
    @0
    @0
    eqid
    nmcvfval
    cU
    @2
    c2nd
    cnnvnm.6
    fveq2i
    @1
    cabs
    caddc
    cmul
    opex
    cc
    cr
    cabs
    wf
    cc
    cvv
    wcel
    cabs
    cvv
    wcel
    absf
    cnex
    cc
    cr
    cvv
    cabs
    fex
    mp2an
    op2nd
    3eqtrri
end
