include "wal.mm"
include "ax-5.mm"
include "hbal.mm"
include "spv.mm"
include "alrimih.mm"
include "weq.mm"
include "wb.mm"
include "equcoms.mm"
include "bicomd.mm"
include "impbii.mm"

theorem cbvalv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  assert |- ( A. x ph <-> A. y ps )

  proof
    wph
    vx
    wal
    #
    wps
    vy
    wal
    #
    @0
    wps
    vy
    wph
    vy
    vx
    wph
    vy
    ax-5
    hbal
    wph
    wps
    vx
    vy
    cbvalv.1
    spv
    alrimih
    @1
    wph
    vx
    wps
    vx
    vy
    wps
    vx
    ax-5
    hbal
    wps
    wph
    vy
    vx
    vy
    vx
    weq
    wph
    wps
    wph
    wps
    wb
    vx
    vy
    cbvalv.1
    equcoms
    bicomd
    spv
    alrimih
    impbii
end
