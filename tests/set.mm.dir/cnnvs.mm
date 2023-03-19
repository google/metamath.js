include "cns.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "eqid.mm"
include "smfval.mm"
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
include "op2nd.mm"
include "3eqtrri.mm"

theorem cnnvs
  let cU: class U
  assume cnnvs.6: |- U = <. <. + , x. >. , abs >.


  assert |- x. = ( .sOLD ` U )

  proof
    cU
    cns
    cfv
    #
    cU
    c1st
    cfv
    #
    c2nd
    cfv
    caddc
    cmul
    cop
    #
    c2nd
    cfv
    cmul
    @0
    cU
    @0
    eqid
    smfval
    @1
    @2
    c2nd
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
    cnnvs.6
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
    op2nd
    3eqtrri
end
