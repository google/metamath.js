include "crg.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmgm.mm"
include "ringmnd.mm"
include "mndmgm.mm"
include "syl.mm"

theorem ringmgm
  let cR: class R


  assert |- ( R e. Ring -> R e. Mgm )

  proof
    cR
    crg
    wcel
    cR
    cmnd
    wcel
    cR
    cmgm
    wcel
    cR
    ringmnd
    cR
    mndmgm
    syl
end
