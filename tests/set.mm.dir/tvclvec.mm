include "ctvc.mm"
include "wcel.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "clvec.mm"
include "tvclmod.mm"
include "ctdrg.mm"
include "eqid.mm"
include "tvctdrg.mm"
include "tdrgdrng.mm"
include "syl.mm"
include "islvec.mm"
include "sylanbrc.mm"

theorem tvclvec
  let cW: class W


  assert |- ( W e. TopVec -> W e. LVec )

  proof
    cW
    ctvc
    wcel
    #
    cW
    clmod
    wcel
    cW
    csca
    cfv
    #
    cdr
    wcel
    #
    cW
    clvec
    wcel
    cW
    tvclmod
    @0
    @1
    ctdrg
    wcel
    @2
    @1
    cW
    @1
    eqid
    #
    tvctdrg
    @1
    tdrgdrng
    syl
    @1
    cW
    @3
    islvec
    sylanbrc
end
