include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "eliun.mm"
include "sylib.mm"

theorem bnj1405
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X
  assume bnj1405.1: |- ( ph -> X e. U_ y e. A B )

  disjoint X y
  assert |- ( ph -> E. y e. A X e. B )

  proof
    wph
    cX
    vy
    cA
    cB
    ciun
    wcel
    cX
    cB
    wcel
    vy
    cA
    wrex
    bnj1405.1
    vy
    cX
    cA
    cB
    eliun
    sylib
end
