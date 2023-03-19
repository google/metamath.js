include "wrex.mm"
include "wceq.mm"
include "wb.mm"
include "rexeqf.mm"
include "syl.mm"
include "rexbid.mm"
include "bitrd.mm"

theorem rexeqbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqbid.0: |- F/ x ph
  assume raleqbid.1: |- F/_ x A
  assume raleqbid.2: |- F/_ x B
  assume raleqbid.3: |- ( ph -> A = B )
  assume raleqbid.4: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) )

  proof
    wph
    wps
    vx
    cA
    wrex
    #
    wps
    vx
    cB
    wrex
    #
    wch
    vx
    cB
    wrex
    wph
    cA
    cB
    wceq
    @0
    @1
    wb
    raleqbid.3
    wps
    vx
    cA
    cB
    raleqbid.1
    raleqbid.2
    rexeqf
    syl
    wph
    wps
    wch
    vx
    cB
    raleqbid.0
    raleqbid.4
    rexbid
    bitrd
end
