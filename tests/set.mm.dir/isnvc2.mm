include "cnvc.mm"
include "wcel.mm"
include "cnlm.mm"
include "clvec.mm"
include "wa.mm"
include "cdr.mm"
include "isnvc.mm"
include "clmod.mm"
include "wb.mm"
include "nlmlmod.mm"
include "islvec.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isnvc2
  let cF: class F
  let cW: class W
  assume isnvc2.1: |- F = ( Scalar ` W )


  assert |- ( W e. NrmVec <-> ( W e. NrmMod /\ F e. DivRing ) )

  proof
    cW
    cnvc
    wcel
    cW
    cnlm
    wcel
    #
    cW
    clvec
    wcel
    #
    wa
    @0
    cF
    cdr
    wcel
    #
    wa
    cW
    isnvc
    @0
    @1
    @2
    @0
    cW
    clmod
    wcel
    #
    @1
    @2
    wb
    cW
    nlmlmod
    @1
    @3
    @2
    cF
    cW
    isnvc2.1
    islvec
    baib
    syl
    pm5.32i
    bitri
end
