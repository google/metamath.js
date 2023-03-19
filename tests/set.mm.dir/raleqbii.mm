include "cv.mm"
include "wcel.mm"
include "eleq2i.mm"
include "imbi12i.mm"
include "ralbii2.mm"

theorem raleqbii
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqbii.1: |- A = B
  assume raleqbii.2: |- ( ps <-> ch )


  assert |- ( A. x e. A ps <-> A. x e. B ch )

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
    raleqbii.1
    eleq2i
    raleqbii.2
    imbi12i
    ralbii2
end
