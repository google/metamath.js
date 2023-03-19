include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "ssint.mm"
include "wcel.mm"
include "sseq2.mm"
include "elrab.mm"
include "simprbi.mm"
include "mprgbir.mm"

theorem ssintub
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let wph: wff ph

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- A C_ |^| { x e. B | A C_ x }

  proof
    cA
    cA
    vx
    cv
    #
    wss
    #
    vx
    cB
    crab
    #
    cint
    wss
    cA
    vy
    cv
    #
    wss
    #
    vy
    @2
    vy
    cA
    @2
    ssint
    @3
    @2
    wcel
    @3
    cB
    wcel
    @4
    @1
    @4
    vx
    @3
    cB
    @0
    @3
    cA
    sseq2
    elrab
    simprbi
    mprgbir
end
