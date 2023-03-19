include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nf5i.mm"
include "dvelimf.mm"
include "nf5rd.mm"

theorem dvelimh
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelimh.1: |- ( ph -> A. x ph )
  assume dvelimh.2: |- ( ps -> A. z ps )
  assume dvelimh.3: |- ( z = y -> ( ph <-> ps ) )


  assert |- ( -. A. x x = y -> ( ps -> A. x ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    wps
    vx
    wph
    wps
    vx
    vy
    vz
    wph
    vx
    dvelimh.1
    nf5i
    wps
    vz
    dvelimh.2
    nf5i
    dvelimh.3
    dvelimf
    nf5rd
end
