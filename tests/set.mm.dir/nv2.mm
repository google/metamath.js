include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "co.mm"
include "c2.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vc2OLD.mm"
include "sylan.mm"

theorem nv2
  let cA: class A
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvdi.1: |- X = ( BaseSet ` U )
  assume nvdi.2: |- G = ( +v ` U )
  assume nvdi.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G A ) = ( 2 S A ) )

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
    cA
    cA
    cG
    co
    c2
    cA
    cS
    co
    wceq
    cU
    @0
    @0
    eqid
    nvvc
    cA
    cS
    cG
    @0
    cX
    cU
    cG
    nvdi.2
    vafval
    cS
    cU
    nvdi.4
    smfval
    cU
    cG
    cX
    nvdi.1
    nvdi.2
    bafval
    vc2OLD
    sylan
end
