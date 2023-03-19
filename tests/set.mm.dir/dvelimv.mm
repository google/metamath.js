include "ax-5.mm"
include "dvelim.mm"

theorem dvelimv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelimv.1: |- ( z = y -> ( ph <-> ps ) )

  disjoint ph x
  disjoint ps z
  assert |- ( -. A. x x = y -> ( ps -> A. x ps ) )

  proof
    wph
    wps
    vx
    vy
    vz
    wph
    vx
    ax-5
    dvelimv.1
    dvelim
end
