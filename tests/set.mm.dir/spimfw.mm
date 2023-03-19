include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "speimfw.mm"
include "df-ex.mm"
include "con1i.mm"
include "sylbi.mm"
include "syl6.mm"

theorem spimfw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spimfw.1: |- ( -. ps -> A. x -. ps )
  assume spimfw.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( -. A. x -. x = y -> ( A. x ph -> ps ) )

  proof
    vx
    vy
    weq
    wn
    vx
    wal
    wn
    wph
    vx
    wal
    wps
    vx
    wex
    #
    wps
    wph
    wps
    vx
    vy
    spimfw.2
    speimfw
    @0
    wps
    wn
    vx
    wal
    #
    wn
    wps
    wps
    vx
    df-ex
    wps
    @1
    spimfw.1
    con1i
    sylbi
    syl6
end
