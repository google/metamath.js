include "cvv.mm"
include "wrex.mm"
include "wex.mm"
include "nfcv.mm"
include "rexcomf.mm"
include "rexv.mm"
include "rexbii.mm"
include "3bitr3i.mm"

theorem rexcom4f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ralcom4f.1: |- F/_ y A

  disjoint x y
  assert |- ( E. x e. A E. y ph <-> E. y E. x e. A ph )

  proof
    wph
    vy
    cvv
    wrex
    #
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    #
    vy
    cvv
    wrex
    wph
    vy
    wex
    #
    vx
    cA
    wrex
    @1
    vy
    wex
    wph
    vx
    vy
    cA
    cvv
    ralcom4f.1
    vx
    cvv
    nfcv
    rexcomf
    @0
    @2
    vx
    cA
    wph
    vy
    rexv
    rexbii
    @1
    vy
    rexv
    3bitr3i
end
