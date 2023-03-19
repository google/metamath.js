include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "cablo.mm"
include "eqid.mm"
include "nvvc.mm"
include "vafval.mm"
include "vcablo.mm"
include "syl.mm"

theorem nvablo
  let cU: class U
  let cG: class G
  assume nvabl.1: |- G = ( +v ` U )


  assert |- ( U e. NrmCVec -> G e. AbelOp )

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
    cG
    cablo
    wcel
    cU
    @0
    @0
    eqid
    nvvc
    cG
    @0
    cU
    cG
    nvabl.1
    vafval
    vcablo
    syl
end
