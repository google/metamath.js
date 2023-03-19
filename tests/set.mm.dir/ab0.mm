include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "nfab1.mm"
include "eq0f.mm"
include "abid.mm"
include "notbii.mm"
include "albii.mm"
include "bitri.mm"

theorem ab0
  let wph: wff ph
  let vx: setvar x


  assert |- ( { x | ph } = (/) <-> A. x -. ph )

  proof
    wph
    vx
    cab
    #
    c0
    wceq
    vx
    cv
    @0
    wcel
    #
    wn
    #
    vx
    wal
    wph
    wn
    #
    vx
    wal
    vx
    @0
    wph
    vx
    nfab1
    eq0f
    @2
    @3
    vx
    @1
    wph
    wph
    vx
    abid
    notbii
    albii
    bitri
end
