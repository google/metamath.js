include "cdrs.mm"
include "wcel.mm"
include "cpreset.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "isdrs.mm"
include "simp2bi.mm"

theorem drsbn0
  let cB: class B
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume drsbn0.b: |- B = ( Base ` K )


  assert |- ( K e. Dirset -> B =/= (/) )

  proof
    cK
    cdrs
    wcel
    cK
    cpreset
    wcel
    cB
    c0
    wne
    vx
    cv
    vz
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    vy
    cv
    @0
    @1
    wbr
    wa
    vz
    cB
    wrex
    vy
    cB
    wral
    vx
    cB
    wral
    vx
    vy
    vz
    cB
    cK
    @1
    drsbn0.b
    @1
    eqid
    isdrs
    simp2bi
end
