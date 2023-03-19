include "cvv.mm"
include "wcel.mm"
include "fabexg.mm"
include "mp2an.mm"

theorem fabex
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume fabex.1: |- A e. _V
  assume fabex.2: |- B e. _V
  assume fabex.3: |- F = { x | ( x : A --> B /\ ph ) }

  disjoint A x
  disjoint B x
  assert |- F e. _V

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cF
    cvv
    wcel
    fabex.1
    fabex.2
    wph
    vx
    cA
    cB
    cvv
    cvv
    cF
    fabex.3
    fabexg
    mp2an
end
