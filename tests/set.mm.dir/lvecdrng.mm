include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "cdr.mm"
include "islvec.mm"
include "simprbi.mm"

theorem lvecdrng
  let cF: class F
  let cW: class W
  let vf: setvar f
  assume islvec.1: |- F = ( Scalar ` W )


  assert |- ( W e. LVec -> F e. DivRing )

  proof
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    cF
    cdr
    wcel
    cF
    cW
    islvec.1
    islvec
    simprbi
end
