include "wal.mm"
include "weq.mm"
include "cbvaldva.mm"
include "cbvalv.mm"

theorem cbval2v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbval2v.1: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint w x
  disjoint y z
  assert |- ( A. x A. y ph <-> A. z A. w ps )

  proof
    wph
    vy
    wal
    wps
    vw
    wal
    vx
    vz
    vx
    vz
    weq
    wph
    wps
    vy
    vw
    cbval2v.1
    cbvaldva
    cbvalv
end
