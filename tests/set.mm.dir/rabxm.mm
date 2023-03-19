include "wn.mm"
include "wo.mm"
include "crab.mm"
include "cun.mm"
include "wceq.mm"
include "rabid2.mm"
include "cv.mm"
include "wcel.mm"
include "exmidd.mm"
include "mprgbir.mm"
include "unrab.mm"
include "eqtr4i.mm"

theorem rabxm
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- A = ( { x e. A | ph } u. { x e. A | -. ph } )

  proof
    cA
    wph
    wph
    wn
    #
    wo
    #
    vx
    cA
    crab
    #
    wph
    vx
    cA
    crab
    @0
    vx
    cA
    crab
    cun
    cA
    @2
    wceq
    @1
    vx
    cA
    @1
    vx
    cA
    rabid2
    vx
    cv
    cA
    wcel
    wph
    exmidd
    mprgbir
    wph
    @0
    vx
    cA
    unrab
    eqtr4i
end
