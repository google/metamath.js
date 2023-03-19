include "ersym.mm"
include "ertrd.mm"

theorem ertr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume ersymb.1: |- ( ph -> R Er X )
  assume ertr4d.5: |- ( ph -> A R B )
  assume ertr4d.6: |- ( ph -> C R B )


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    cX
    ersymb.1
    ertr4d.5
    wph
    cC
    cB
    cR
    cX
    ersymb.1
    ertr4d.6
    ersym
    ertrd
end
