include "ertrd.mm"
include "ersym.mm"

theorem ertr2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume ersymb.1: |- ( ph -> R Er X )
  assume ertrd.5: |- ( ph -> A R B )
  assume ertrd.6: |- ( ph -> B R C )


  assert |- ( ph -> C R A )

  proof
    wph
    cA
    cC
    cR
    cX
    ersymb.1
    wph
    cA
    cB
    cC
    cR
    cX
    ersymb.1
    ertrd.5
    ertrd.6
    ertrd
    ersym
end
