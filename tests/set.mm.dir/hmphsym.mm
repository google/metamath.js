include "chmph.mm"
include "wbr.mm"
include "cv.mm"
include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "hmph.mm"
include "n0.mm"
include "bitri.mm"
include "ccnv.mm"
include "hmeocnv.mm"
include "hmphi.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem hmphsym
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let cL: class L


  assert |- ( J ~= K -> K ~= J )

  proof
    cJ
    cK
    chmph
    wbr
    #
    vf
    cv
    #
    cJ
    cK
    chmeo
    co
    #
    wcel
    #
    vf
    wex
    #
    cK
    cJ
    chmph
    wbr
    #
    @0
    @2
    c0
    wne
    @4
    cJ
    cK
    hmph
    vf
    @2
    n0
    bitri
    @3
    @5
    vf
    @3
    @1
    ccnv
    #
    cK
    cJ
    chmeo
    co
    wcel
    @5
    @1
    cJ
    cK
    hmeocnv
    @6
    cK
    cJ
    hmphi
    syl
    exlimiv
    sylbi
end
