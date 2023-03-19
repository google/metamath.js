include "cvv.mm"
include "wcel.mm"
include "crisc.mm"
include "wbr.mm"
include "crngo.mm"
include "wa.mm"
include "cv.mm"
include "crngiso.mm"
include "co.mm"
include "wex.mm"
include "wb.mm"
include "isriscg.mm"
include "mp2an.mm"

theorem isrisc
  let cR: class R
  let cS: class S
  let vf: setvar f
  assume isrisc.1: |- R e. _V
  assume isrisc.2: |- S e. _V

  disjoint R f
  disjoint S f
  assert |- ( R ~=R S <-> ( ( R e. RingOps /\ S e. RingOps ) /\ E. f f e. ( R RngIso S ) ) )

  proof
    cR
    cvv
    wcel
    cS
    cvv
    wcel
    cR
    cS
    crisc
    wbr
    cR
    crngo
    wcel
    cS
    crngo
    wcel
    wa
    vf
    cv
    cR
    cS
    crngiso
    co
    wcel
    vf
    wex
    wa
    wb
    isrisc.1
    isrisc.2
    cvv
    cvv
    cR
    cS
    vf
    isriscg
    mp2an
end
