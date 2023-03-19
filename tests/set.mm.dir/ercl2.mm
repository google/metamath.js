include "ersym.mm"
include "ercl.mm"

theorem ercl2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume ersym.1: |- ( ph -> R Er X )
  assume ersym.2: |- ( ph -> A R B )


  assert |- ( ph -> B e. X )

  proof
    wph
    cB
    cA
    cR
    cX
    ersym.1
    wph
    cA
    cB
    cR
    cX
    ersym.1
    ersym.2
    ersym
    ercl
end
