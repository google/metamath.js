include "crio.mm"
include "riotabidv.mm"
include "riotaeqdv.mm"
include "eqtrd.mm"

theorem riotaeqbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riotaeqbidv.1: |- ( ph -> A = B )
  assume riotaeqbidv.2: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ch ) )

  proof
    wph
    wps
    vx
    cA
    crio
    wch
    vx
    cA
    crio
    wch
    vx
    cB
    crio
    wph
    wps
    wch
    vx
    cA
    riotaeqbidv.2
    riotabidv
    wph
    wch
    vx
    cA
    cB
    riotaeqbidv.1
    riotaeqdv
    eqtrd
end
