include "wn.mm"
include "wal.mm"
include "wex.mm"
include "alrimiv.mm"
include "alnex.mm"
include "sylib.mm"

theorem nexdvOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nexdv.1: |- ( ph -> -. ps )

  disjoint ph x
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
    nexdv.1
    alrimiv
    wps
    vx
    alnex
    sylib
end
