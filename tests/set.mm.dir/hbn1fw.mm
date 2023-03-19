include "wal.mm"
include "wn.mm"
include "cbvalw.mm"
include "notbii.mm"
include "hbxfrbi.mm"

theorem hbn1fw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume hbn1fw.1: |- ( A. x ph -> A. y A. x ph )
  assume hbn1fw.2: |- ( -. ps -> A. x -. ps )
  assume hbn1fw.3: |- ( A. y ps -> A. x A. y ps )
  assume hbn1fw.4: |- ( -. ph -> A. y -. ph )
  assume hbn1fw.5: |- ( -. A. y ps -> A. x -. A. y ps )
  assume hbn1fw.6: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( -. A. x ph -> A. x -. A. x ph )

  proof
    wph
    vx
    wal
    #
    wn
    wps
    vy
    wal
    #
    wn
    vx
    @0
    @1
    wph
    wps
    vx
    vy
    hbn1fw.1
    hbn1fw.2
    hbn1fw.3
    hbn1fw.4
    hbn1fw.6
    cbvalw
    notbii
    hbn1fw.5
    hbxfrbi
end
