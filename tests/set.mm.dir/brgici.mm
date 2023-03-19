include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cgic.mm"
include "wbr.mm"
include "ne0i.mm"
include "brgic.mm"
include "sylibr.mm"

theorem brgici
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R GrpIso S ) -> R ~=g S )

  proof
    cF
    cR
    cS
    cgim
    co
    #
    wcel
    @0
    c0
    wne
    cR
    cS
    cgic
    wbr
    @0
    cF
    ne0i
    cR
    cS
    brgic
    sylibr
end
