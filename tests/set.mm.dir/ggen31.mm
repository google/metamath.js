include "wal.mm"
include "wi.mm"
include "wa.mm"
include "imp.mm"
include "alrimdv.mm"
include "ex.mm"

theorem ggen31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume ggen31.1: |- ( ph -> ( ps -> ( ch -> th ) ) )

  disjoint ch x
  disjoint ph x
  disjoint ps x
  assert |- ( ph -> ( ps -> ( ch -> A. x th ) ) )

  proof
    wph
    wps
    wch
    wth
    vx
    wal
    wi
    wph
    wps
    wa
    wch
    wth
    vx
    wph
    wps
    wch
    wth
    wi
    ggen31.1
    imp
    alrimdv
    ex
end
