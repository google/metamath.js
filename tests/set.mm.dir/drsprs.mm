include "cdrs.mm"
include "wcel.mm"
include "cpreset.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "isdrs.mm"
include "simp1bi.mm"

theorem drsprs
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( K e. Dirset -> K e. Preset )

  proof
    cK
    cdrs
    wcel
    cK
    cpreset
    wcel
    cK
    cbs
    cfv
    #
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
    @1
    @2
    wbr
    wa
    vz
    @0
    wrex
    vy
    @0
    wral
    vx
    @0
    wral
    vx
    vy
    vz
    @0
    cK
    @2
    @0
    eqid
    @2
    eqid
    isdrs
    simp1bi
end
