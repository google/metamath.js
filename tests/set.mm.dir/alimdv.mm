include "ax-5.mm"
include "alimdh.mm"

theorem alimdv
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume alimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( A. x ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    ax-5
    alimdv.1
    alimdh
end
