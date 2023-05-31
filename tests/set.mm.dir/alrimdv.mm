include "ax-5.mm"
include "alrimdh.mm"

theorem alrimdv
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume alrimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  disjoint ps x
  assert |- ( ph -> ( ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    ax-5
    wps
    vx
    ax-5
    alrimdv.1
    alrimdh
end
