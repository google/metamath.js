include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "df-lvec.mm"
include "elrab2.mm"

theorem islvec
  let cF: class F
  let cW: class W
  let vf: setvar f
  assume islvec.1: |- F = ( Scalar ` W )


  assert |- ( W e. LVec <-> ( W e. LMod /\ F e. DivRing ) )

  proof
    vf
    cv
    #
    csca
    cfv
    #
    cdr
    wcel
    cF
    cdr
    wcel
    vf
    cW
    clmod
    clvec
    @0
    cW
    wceq
    #
    @1
    cF
    cdr
    @2
    @1
    cW
    csca
    cfv
    cF
    @0
    cW
    csca
    fveq2
    islvec.1
    syl6eqr
    eleq1d
    vf
    df-lvec
    elrab2
end
