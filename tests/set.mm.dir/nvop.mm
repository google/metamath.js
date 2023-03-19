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
include "opeq2i.mm"
include "eqid.mm"
include "nvvop.mm"
include "opeq1d.mm"
include "syl5eqr.mm"
include "eqtrd.mm"

theorem nvop
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  assume nvop.2: |- G = ( +v ` U )
  assume nvop.4: |- S = ( .sOLD ` U )
  assume nvop.6: |- N = ( normCV ` U )


  assert |- ( U e. NrmCVec -> U = <. <. G , S >. , N >. )

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
    cG
    cS
    cop
    #
    cN
    cop
    #
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
    @0
    @3
    @1
    cN
    cop
    @5
    cN
    @2
    @1
    cU
    cN
    nvop.6
    nmcvfval
    opeq2i
    @0
    @1
    @4
    cN
    cS
    cU
    cG
    @1
    @1
    eqid
    nvop.2
    nvop.4
    nvvop
    opeq1d
    syl5eqr
    eqtrd
end
