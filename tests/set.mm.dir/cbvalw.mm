include "wal.mm"
include "weq.mm"
include "biimpd.mm"
include "cbvaliw.mm"
include "wi.mm"
include "biimprd.mm"
include "equcoms.mm"
include "impbii.mm"

theorem cbvalw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalw.1: |- ( A. x ph -> A. y A. x ph )
  assume cbvalw.2: |- ( -. ps -> A. x -. ps )
  assume cbvalw.3: |- ( A. y ps -> A. x A. y ps )
  assume cbvalw.4: |- ( -. ph -> A. y -. ph )
  assume cbvalw.5: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( A. x ph <-> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    wal
    wph
    wps
    vx
    vy
    cbvalw.1
    cbvalw.2
    vx
    vy
    weq
    #
    wph
    wps
    cbvalw.5
    biimpd
    cbvaliw
    wps
    wph
    vy
    vx
    cbvalw.3
    cbvalw.4
    wps
    wph
    wi
    vx
    vy
    @0
    wph
    wps
    cbvalw.5
    biimprd
    equcoms
    cbvaliw
    impbii
end
