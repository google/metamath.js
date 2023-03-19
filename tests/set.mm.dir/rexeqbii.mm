include "cv.mm"
include "wcel.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "rexbii2.mm"

theorem rexeqbii
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rexeqbii.1: |- A = B
  assume rexeqbii.2: |- ( ps <-> ch )


  assert |- ( E. x e. A ps <-> E. x e. B ch )

  proof
    wps
    wch
    vx
    cA
    cB
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wps
    wch
    cA
    cB
    @0
    rexeqbii.1
    eleq2i
    rexeqbii.2
    anbi12i
    rexbii2
end
