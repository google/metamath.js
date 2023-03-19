include "wbr.mm"
include "ertr.mm"
include "mp2and.mm"

theorem ertrd
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


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cR
    wbr
    cB
    cC
    cR
    wbr
    cA
    cC
    cR
    wbr
    ertrd.5
    ertrd.6
    wph
    cA
    cB
    cC
    cR
    cX
    ersymb.1
    ertr
    mp2and
end
