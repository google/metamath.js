include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cmnd.mm"
include "srgcmn.mm"
include "cmnmnd.mm"
include "syl.mm"

theorem srgmnd
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. SRing -> R e. Mnd )

  proof
    cR
    csrg
    wcel
    cR
    ccmn
    wcel
    cR
    cmnd
    wcel
    cR
    srgcmn
    cR
    cmnmnd
    syl
end
