include "wsb.mm"
include "sbco3.mm"
include "sbcom3.mm"
include "3bitr3i.mm"

theorem sbcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph )

  proof
    wph
    vx
    vz
    wsb
    vz
    vy
    wsb
    wph
    vz
    vx
    wsb
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    vz
    vy
    wsb
    wph
    vz
    vy
    wsb
    vx
    vy
    wsb
    wph
    vx
    vz
    vy
    sbco3
    wph
    vx
    vz
    vy
    sbcom3
    wph
    vz
    vx
    vy
    sbcom3
    3bitr3i
end
