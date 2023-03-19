include "wal.mm"
include "ax-5.mm"
include "wn.mm"
include "hbn1fw.mm"

theorem hbn1w
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume hbn1w.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( -. A. x ph -> A. x -. A. x ph )

  proof
    wph
    wps
    vx
    vy
    wph
    vx
    wal
    vy
    ax-5
    wps
    wn
    vx
    ax-5
    wps
    vy
    wal
    #
    vx
    ax-5
    wph
    wn
    vy
    ax-5
    @0
    wn
    vx
    ax-5
    hbn1w.1
    hbn1fw
end
