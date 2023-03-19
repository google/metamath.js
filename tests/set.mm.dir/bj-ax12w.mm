include "wal.mm"
include "wi.mm"
include "spw.mm"
include "bj-ax12wlem.mm"
include "syl5.mm"

theorem bj-ax12w
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bj-ax12w.1: |- ( ph -> ( ps <-> ch ) )
  assume bj-ax12w.2: |- ( y = z -> ( ps <-> th ) )

  disjoint ch x
  disjoint th y
  disjoint ps z
  disjoint y z
  assert |- ( ph -> ( A. y ps -> A. x ( ph -> ps ) ) )

  proof
    wps
    vy
    wal
    wps
    wph
    wph
    wps
    wi
    vx
    wal
    wps
    wth
    vy
    vz
    bj-ax12w.2
    spw
    wph
    wps
    wch
    vx
    bj-ax12w.1
    bj-ax12wlem
    syl5
end
