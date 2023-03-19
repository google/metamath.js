include "nf5ri.mm"
include "alimdh.mm"

theorem alimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alimd.1: |- F/ x ph
  assume alimd.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( A. x ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    alimd.1
    nf5ri
    alimd.2
    alimdh
end
