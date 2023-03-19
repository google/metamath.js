include "ax-5.mm"
include "dvelimh.mm"

theorem dvelim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelim.1: |- ( ph -> A. x ph )
  assume dvelim.2: |- ( z = y -> ( ph <-> ps ) )

  disjoint ps z
  assert |- ( -. A. x x = y -> ( ps -> A. x ps ) )

  proof
    wph
    wps
    vx
    vy
    vz
    dvelim.1
    wps
    vz
    ax-5
    dvelim.2
    dvelimh
end
