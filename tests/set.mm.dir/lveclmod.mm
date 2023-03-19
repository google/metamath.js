include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "eqid.mm"
include "islvec.mm"
include "simplbi.mm"

theorem lveclmod
  let cW: class W


  assert |- ( W e. LVec -> W e. LMod )

  proof
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    cW
    csca
    cfv
    #
    cdr
    wcel
    @0
    cW
    @0
    eqid
    islvec
    simplbi
end
