include "clmic.mm"
include "clmim.mm"
include "clmod.mm"
include "cxp.mm"
include "df-lmic.mm"
include "lmimfn.mm"
include "brwitnlem.mm"

theorem brlmic
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F


  assert |- ( R ~=m S <-> ( R LMIso S ) =/= (/) )

  proof
    cR
    cS
    clmic
    clmim
    clmod
    clmod
    cxp
    df-lmic
    lmimfn
    brwitnlem
end
