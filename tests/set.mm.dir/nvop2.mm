include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wrel.mm"
include "wceq.mm"
include "nvrel.mm"
include "1st2nd.mm"
include "mpan.mm"
include "nmcvfval.mm"
include "opeq12i.mm"
include "syl6eqr.mm"

theorem nvop2
  let cU: class U
  let cN: class N
  let cW: class W
  assume nvop2.1: |- W = ( 1st ` U )
  assume nvop2.6: |- N = ( normCV ` U )


  assert |- ( U e. NrmCVec -> U = <. W , N >. )

  proof
    cU
    cnv
    wcel
    #
    cU
    cU
    c1st
    cfv
    #
    cU
    c2nd
    cfv
    #
    cop
    #
    cW
    cN
    cop
    cnv
    wrel
    @0
    cU
    @3
    wceq
    nvrel
    cU
    cnv
    1st2nd
    mpan
    cW
    @1
    cN
    @2
    nvop2.1
    cU
    cN
    nvop2.6
    nmcvfval
    opeq12i
    syl6eqr
end
