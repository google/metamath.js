include "cpv.mm"
include "cfv.mm"
include "c1st.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "eqid.mm"
include "vafval.mm"
include "cabs.mm"
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
include "op1st.mm"
include "eqtri.mm"
include "addex.mm"
include "mulex.mm"
include "3eqtrri.mm"

theorem cnnvg
  let cU: class U
  assume cnnvg.6: |- U = <. <. + , x. >. , abs >.


  assert |- + = ( +v ` U )

  proof
    cU
    cpv
    cfv
    #
    cU
    c1st
    cfv
    #
    c1st
    cfv
    caddc
    cmul
    cop
    #
    c1st
    cfv
    caddc
    cU
    @0
    @0
    eqid
    vafval
    @1
    @2
    c1st
    @1
    @2
    cabs
    cop
    #
    c1st
    cfv
    @2
    cU
    @3
    c1st
    cnnvg.6
    fveq2i
    @2
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
    op1st
    eqtri
    fveq2i
    caddc
    cmul
    addex
    mulex
    op1st
    3eqtrri
end
