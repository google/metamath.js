include "wal.mm"
include "wi.mm"
include "alim.mm"
include "weq.mm"
include "biimprd.mm"
include "equcoms.mm"
include "spimw.mm"
include "syl56.mm"
include "biimpd.mm"
include "mpg.mm"

theorem spfwOLD
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
    #
    wps
    wi
    #
    @0
    wph
    wi
    vy
    @0
    @0
    vy
    wal
    @1
    vy
    wal
    wps
    vy
    wal
    wph
    spfw.2
    @0
    wps
    vy
    alim
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
    vx
    vy
    weq
    #
    wph
    wps
    spfw.4
    biimprd
    equcoms
    spimw
    syl56
    wph
    wps
    vx
    vy
    spfw.1
    @2
    wph
    wps
    spfw.4
    biimpd
    spimw
    mpg
end
