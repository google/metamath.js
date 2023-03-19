include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "clmic.mm"
include "wbr.mm"
include "ne0i.mm"
include "brlmic.mm"
include "sylibr.mm"

theorem brlmici
  let cR: class R
  let cS: class S
  let cF: class F
  let vf: setvar f


  assert |- ( F e. ( R LMIso S ) -> R ~=m S )

  proof
    cF
    cR
    cS
    clmim
    co
    #
    wcel
    @0
    c0
    wne
    cR
    cS
    clmic
    wbr
    @0
    cF
    ne0i
    cR
    cS
    brlmic
    sylibr
end
