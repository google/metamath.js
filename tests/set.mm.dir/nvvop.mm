include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cvc.mm"
include "wrel.mm"
include "wceq.mm"
include "vcrel.mm"
include "cnmcv.mm"
include "cvv.mm"
include "cxp.mm"
include "nvss.mm"
include "eqid.mm"
include "nvop2.mm"
include "eleq1d.mm"
include "ibi.mm"
include "sseldi.mm"
include "opelxp1.mm"
include "syl.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "vafval.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "smfval.mm"
include "opeq12i.mm"
include "syl6eqr.mm"

theorem nvvop
  let cS: class S
  let cU: class U
  let cG: class G
  let cW: class W
  assume nvvop.1: |- W = ( 1st ` U )
  assume nvvop.2: |- G = ( +v ` U )
  assume nvvop.4: |- S = ( .sOLD ` U )


  assert |- ( U e. NrmCVec -> W = <. G , S >. )

  proof
    cU
    cnv
    wcel
    #
    cW
    cW
    c1st
    cfv
    #
    cW
    c2nd
    cfv
    #
    cop
    #
    cG
    cS
    cop
    @0
    cvc
    wrel
    cW
    cvc
    wcel
    #
    cW
    @3
    wceq
    vcrel
    @0
    cW
    cU
    cnmcv
    cfv
    #
    cop
    #
    cvc
    cvv
    cxp
    #
    wcel
    @4
    @0
    cnv
    @7
    @6
    nvss
    @0
    @6
    cnv
    wcel
    @0
    cU
    @6
    cnv
    cU
    @5
    cW
    nvvop.1
    @5
    eqid
    nvop2
    eleq1d
    ibi
    sseldi
    cW
    @5
    cvc
    cvv
    opelxp1
    syl
    cW
    cvc
    1st2nd
    sylancr
    cG
    @1
    cS
    @2
    cG
    cU
    c1st
    cfv
    #
    c1st
    cfv
    @1
    cU
    cG
    nvvop.2
    vafval
    cW
    @8
    c1st
    nvvop.1
    fveq2i
    eqtr4i
    cS
    @8
    c2nd
    cfv
    @2
    cS
    cU
    nvvop.4
    smfval
    cW
    @8
    c2nd
    nvvop.1
    fveq2i
    eqtr4i
    opeq12i
    syl6eqr
end
