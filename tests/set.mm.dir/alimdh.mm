include "wal.mm"
include "wi.mm"
include "al2imi.mm"
include "syl.mm"

theorem alimdh
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alimdh.1: |- ( ph -> A. x ph )
  assume alimdh.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( A. x ps -> A. x ch ) )

  proof
    wph
    wph
    vx
    wal
    wps
    vx
    wal
    wch
    vx
    wal
    wi
    alimdh.1
    wph
    wps
    wch
    vx
    alimdh.2
    al2imi
    syl
end
