include "wn.mm"
include "wal.mm"
include "wex.mm"
include "alrimih.mm"
include "alnex.mm"
include "sylib.mm"

theorem nexdh
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nexdh.1: |- ( ph -> A. x ph )
  assume nexdh.2: |- ( ph -> -. ps )


  assert |- ( ph -> -. E. x ps )

  proof
    wph
    wps
    wn
    #
    vx
    wal
    wps
    vx
    wex
    wn
    wph
    @0
    vx
    nexdh.1
    nexdh.2
    alrimih
    wps
    vx
    alnex
    sylib
end
