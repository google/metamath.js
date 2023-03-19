include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "crisc.mm"
include "wbr.mm"
include "cv.mm"
include "crngiso.mm"
include "co.mm"
include "wex.mm"
include "isriscg.mm"
include "bianabs.mm"

theorem risc
  let cR: class R
  let cS: class S
  let vf: setvar f

  disjoint R f
  disjoint S f
  assert |- ( ( R e. RingOps /\ S e. RingOps ) -> ( R ~=R S <-> E. f f e. ( R RngIso S ) ) )

  proof
    cR
    crngo
    wcel
    cS
    crngo
    wcel
    wa
    cR
    cS
    crisc
    wbr
    vf
    cv
    cR
    cS
    crngiso
    co
    wcel
    vf
    wex
    crngo
    crngo
    cR
    cS
    vf
    isriscg
    bianabs
end
