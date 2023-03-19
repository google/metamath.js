include "c0.mm"
include "ccnv.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "br0.mm"
include "intnan.mm"
include "nex.mm"
include "copab.mm"
include "cab.mm"
include "df-cnv.mm"
include "df-opab.mm"
include "eqtri.mm"
include "abeq2i.mm"
include "mtbir.mm"
include "nel0.mm"

theorem cnv0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' (/) = (/)

  proof
    vx
    c0
    ccnv
    #
    vx
    cv
    #
    @0
    wcel
    @1
    vz
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    @3
    @2
    c0
    wbr
    #
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    @7
    vz
    @6
    vy
    @5
    @4
    @3
    @2
    br0
    intnan
    nex
    nex
    @8
    vx
    @0
    @0
    @5
    vz
    vy
    copab
    @8
    vx
    cab
    vz
    vy
    c0
    df-cnv
    @5
    vz
    vy
    vx
    df-opab
    eqtri
    abeq2i
    mtbir
    nel0
end
