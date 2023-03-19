include "crngo.mm"
include "wcel.mm"
include "crngiso.mm"
include "co.mm"
include "crisc.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "elex2.mm"
include "risc.mm"
include "syl5ibr.mm"
include "3impia.mm"

theorem risci
  let cR: class R
  let cS: class S
  let cF: class F
  let vf: setvar f


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngIso S ) ) -> R ~=R S )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crngiso
    co
    #
    wcel
    #
    cR
    cS
    crisc
    wbr
    #
    @3
    @4
    @0
    @1
    wa
    vf
    cv
    @2
    wcel
    vf
    wex
    vf
    cF
    @2
    elex2
    cR
    cS
    vf
    risc
    syl5ibr
    3impia
end
