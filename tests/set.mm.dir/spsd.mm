include "wal.mm"
include "sp.mm"
include "syl5.mm"

theorem spsd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume spsd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( A. x ps -> ch ) )

  proof
    wps
    vx
    wal
    wps
    wph
    wch
    wps
    vx
    sp
    spsd.1
    syl5
end
