include "cal.mm"
include "wcel.mm"
include "clat.mm"
include "cdm.mm"
include "cv.mm"
include "cp0.mm"
include "cfv.mm"
include "wne.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "isatl.mm"
include "simp2bi.mm"

theorem atl0dm
  let cB: class B
  let cU: class U
  let cG: class G
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume atl01dm.b: |- B = ( Base ` K )
  assume atl01dm.u: |- U = ( lub ` K )
  assume atl01dm.g: |- G = ( glb ` K )


  assert |- ( K e. AtLat -> B e. dom G )

  proof
    cK
    cal
    wcel
    cK
    clat
    wcel
    cB
    cG
    cdm
    wcel
    vx
    cv
    #
    cK
    cp0
    cfv
    #
    wne
    vy
    cv
    @0
    cK
    cple
    cfv
    #
    wbr
    vy
    cK
    catm
    cfv
    #
    wrex
    wi
    vx
    cB
    wral
    vx
    vy
    @3
    cB
    cG
    cK
    @2
    @1
    atl01dm.b
    atl01dm.g
    @2
    eqid
    @1
    eqid
    @3
    eqid
    isatl
    simp2bi
end
