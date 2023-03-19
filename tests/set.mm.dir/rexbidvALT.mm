include "nfv.mm"
include "rexbid.mm"

theorem rexbidvALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    nfv
    rexbidv.1
    rexbid
end
