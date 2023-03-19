include "wal.mm"
include "alimdh.mm"
include "syl5.mm"

theorem alrimdh
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume alrimdh.1: |- ( ph -> A. x ph )
  assume alrimdh.2: |- ( ps -> A. x ps )
  assume alrimdh.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> A. x ch ) )

  proof
    wps
    wps
    vx
    wal
    wph
    wch
    vx
    wal
    alrimdh.2
    wph
    wps
    wch
    vx
    alrimdh.1
    alrimdh.3
    alimdh
    syl5
end
