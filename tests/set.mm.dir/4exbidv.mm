include "wex.mm"
include "2exbidv.mm"

theorem 4exbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume 4exbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  assert |- ( ph -> ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) )

  proof
    wph
    wps
    vw
    wex
    vz
    wex
    wch
    vw
    wex
    vz
    wex
    vx
    vy
    wph
    wps
    wch
    vz
    vw
    4exbidv.1
    2exbidv
    2exbidv
end
