include "nfv.mm"
include "cbvab.mm"

theorem cbvabv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvabv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  assert |- { x | ph } = { y | ps }

  proof
    wph
    wps
    vx
    vy
    wph
    vy
    nfv
    wps
    vx
    nfv
    cbvabv.1
    cbvab
end
