include "wex.mm"
include "exbidv.mm"
include "2exbidv.mm"

theorem 3exbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume 3exbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) )

  proof
    wph
    wps
    vz
    wex
    wch
    vz
    wex
    vx
    vy
    wph
    wps
    wch
    vz
    3exbidv.1
    exbidv
    2exbidv
end
