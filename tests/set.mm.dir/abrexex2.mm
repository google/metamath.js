include "cvv.mm"
include "wcel.mm"
include "cab.mm"
include "wral.mm"
include "wrex.mm"
include "rgenw.mm"
include "abrexex2g.mm"
include "mp2an.mm"

theorem abrexex2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume abrexex2.1: |- A e. _V
  assume abrexex2.2: |- { y | ph } e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- { y | E. x e. A ph } e. _V

  proof
    cA
    cvv
    wcel
    wph
    vy
    cab
    cvv
    wcel
    #
    vx
    cA
    wral
    wph
    vx
    cA
    wrex
    vy
    cab
    cvv
    wcel
    abrexex2.1
    @0
    vx
    cA
    abrexex2.2
    rgenw
    wph
    vx
    vy
    cA
    cvv
    cvv
    abrexex2g
    mp2an
end
