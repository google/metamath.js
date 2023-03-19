include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "mo2v.mm"
include "cv.mm"
include "csn.mm"
include "wss.mm"
include "abss.mm"
include "velsn.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitri.mm"
include "snex.mm"
include "ssex.mm"
include "sylbir.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem moabex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E* x ph -> { x | ph } e. _V )

  proof
    wph
    vx
    wmo
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    cab
    #
    cvv
    wcel
    #
    wph
    vx
    vy
    mo2v
    @2
    @4
    vy
    @2
    @3
    vy
    cv
    #
    csn
    #
    wss
    #
    @4
    @7
    wph
    vx
    cv
    @6
    wcel
    #
    wi
    #
    vx
    wal
    @2
    wph
    vx
    @6
    abss
    @9
    @1
    vx
    @8
    @0
    wph
    vx
    @5
    velsn
    imbi2i
    albii
    bitri
    @3
    @6
    @5
    snex
    ssex
    sylbir
    exlimiv
    sylbi
end
