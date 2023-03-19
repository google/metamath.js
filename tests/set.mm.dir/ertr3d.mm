include "ersym.mm"
include "ertrd.mm"

theorem ertr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume ersymb.1: |- ( ph -> R Er X )
  assume ertr3d.5: |- ( ph -> B R A )
  assume ertr3d.6: |- ( ph -> B R C )


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    cX
    ersymb.1
    wph
    cB
    cA
    cR
    cX
    ersymb.1
    ertr3d.5
    ersym
    ertr3d.6
    ertrd
end
