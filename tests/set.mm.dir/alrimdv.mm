include "ax-5.mm"
include "alrimdh.mm"

theorem alrimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
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
