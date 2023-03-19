include "wal.mm"
include "wa.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"

theorem wl-alanbii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume wl-alanbii.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( A. x ph <-> ( A. x ps /\ A. x ch ) )

  proof
    wph
    vx
    wal
    wps
    wch
    wa
    #
    vx
    wal
    wps
    vx
    wal
    wch
    vx
    wal
    wa
    wph
    @0
    vx
    wl-alanbii.1
    albii
    wps
    wch
    vx
    19.26
    bitri
end
