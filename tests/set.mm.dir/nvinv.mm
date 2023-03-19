include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcm.mm"
include "sylan.mm"

theorem nvinv
  let cA: class A
  let cS: class S
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvinv.1: |- X = ( BaseSet ` U )
  assume nvinv.2: |- G = ( +v ` U )
  assume nvinv.4: |- S = ( .sOLD ` U )
  assume nvinv.5: |- M = ( inv ` G )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( -u 1 S A ) = ( M ` A ) )

  proof
    cU
    cnv
    wcel
    cU
    c1st
    cfv
    #
    cvc
    wcel
    cA
    cX
    wcel
    c1
    cneg
    cA
    cS
    co
    cA
    cM
    cfv
    wceq
    cU
    @0
    @0
    eqid
    nvvc
    cA
    cS
    cG
    cM
    @0
    cX
    cU
    cG
    nvinv.2
    vafval
    cS
    cU
    nvinv.4
    smfval
    cU
    cG
    cX
    nvinv.1
    nvinv.2
    bafval
    nvinv.5
    vcm
    sylan
end
