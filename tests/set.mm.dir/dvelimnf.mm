include "nfv.mm"
include "dvelimf.mm"

theorem dvelimnf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelimnf.1: |- F/ x ph
  assume dvelimnf.2: |- ( z = y -> ( ph <-> ps ) )

  disjoint ps z
  assert |- ( -. A. x x = y -> F/ x ps )

  proof
    wph
    wps
    vx
    vy
    vz
    dvelimnf.1
    wps
    vz
    nfv
    dvelimnf.2
    dvelimf
end
