include "clnm.mm"
include "wcel.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "wral.mm"
include "clmod.mm"
include "islnm.mm"
include "simprbi.mm"
include "wceq.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem lnmlssfg
  let cR: class R
  let cS: class S
  let cU: class U
  let cM: class M
  let va: setvar a
  assume lnmlssfg.s: |- S = ( LSubSp ` M )
  assume lnmlssfg.r: |- R = ( M |`s U )


  assert |- ( ( M e. LNoeM /\ U e. S ) -> R e. LFinGen )

  proof
    cM
    clnm
    wcel
    #
    cM
    va
    cv
    #
    cress
    co
    #
    clfig
    wcel
    #
    va
    cS
    wral
    #
    cU
    cS
    wcel
    cR
    clfig
    wcel
    #
    @0
    cM
    clmod
    wcel
    @4
    cS
    va
    cM
    lnmlssfg.s
    islnm
    simprbi
    @3
    @5
    va
    cU
    cS
    @1
    cU
    wceq
    #
    @2
    cR
    clfig
    @6
    @2
    cM
    cU
    cress
    co
    cR
    @1
    cU
    cM
    cress
    oveq2
    lnmlssfg.r
    syl6eqr
    eleq1d
    rspcv
    mpan9
end
