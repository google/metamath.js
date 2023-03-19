include "cric.mm"
include "wbr.mm"
include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "crs.mm"
include "co.mm"
include "wex.mm"
include "cgic.mm"
include "brric2.mm"
include "cgim.mm"
include "rimgim.mm"
include "brgici.mm"
include "syl.mm"
include "exlimiv.mm"
include "adantl.mm"
include "sylbi.mm"

theorem ricgic
  let cR: class R
  let cS: class S
  let vf: setvar f


  assert |- ( R ~=r S -> R ~=g S )

  proof
    cR
    cS
    cric
    wbr
    cR
    crg
    wcel
    cS
    crg
    wcel
    wa
    #
    vf
    cv
    #
    cR
    cS
    crs
    co
    wcel
    #
    vf
    wex
    #
    wa
    cR
    cS
    cgic
    wbr
    #
    cR
    cS
    vf
    brric2
    @3
    @4
    @0
    @2
    @4
    vf
    @2
    @1
    cR
    cS
    cgim
    co
    wcel
    @4
    cR
    cS
    @1
    rimgim
    cR
    cS
    @1
    brgici
    syl
    exlimiv
    adantl
    sylbi
end
