include "wal.mm"
include "alrimdv.mm"

theorem ggen22
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume ggen22.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps y
  assert |- ( ph -> ( ps -> A. x A. y ch ) )

  proof
    wph
    wps
    wch
    vy
    wal
    vx
    wph
    wps
    wch
    vy
    ggen22.1
    alrimdv
    alrimdv
end
