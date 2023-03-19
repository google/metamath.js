include "wal.mm"
include "weq.mm"
include "biimpd.mm"
include "cbvaliw.mm"
include "wi.mm"
include "biimprd.mm"
include "equcoms.mm"
include "spimw.mm"
include "syl.mm"

theorem spfw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spfw.1: |- ( -. ps -> A. x -. ps )
  assume spfw.2: |- ( A. x ph -> A. y A. x ph )
  assume spfw.3: |- ( -. ph -> A. y -. ph )
  assume spfw.4: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wal
    wps
    vy
    wal
    wph
    wph
    wps
    vx
    vy
    spfw.2
    spfw.1
    vx
    vy
    weq
    #
    wph
    wps
    spfw.4
    biimpd
    cbvaliw
    wps
    wph
    vy
    vx
    spfw.3
    wps
    wph
    wi
    vx
    vy
    @0
    wph
    wps
    spfw.4
    biimprd
    equcoms
    spimw
    syl
end
