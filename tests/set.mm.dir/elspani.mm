include "chil.mm"
include "wss.mm"
include "cspn.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "spanval.mm"
include "eleq2d.mm"
include "elintrab.mm"
include "syl6bb.mm"

theorem elspani
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elspan.1: |- B e. _V

  disjoint A x
  disjoint B x
  assert |- ( A C_ ~H -> ( B e. ( span ` A ) <-> A. x e. SH ( A C_ x -> B e. x ) ) )

  proof
    cA
    chil
    wss
    #
    cB
    cA
    cspn
    cfv
    #
    wcel
    cB
    cA
    vx
    cv
    #
    wss
    #
    vx
    csh
    crab
    cint
    #
    wcel
    @3
    cB
    @2
    wcel
    wi
    vx
    csh
    wral
    @0
    @1
    @4
    cB
    vx
    cA
    spanval
    eleq2d
    @3
    vx
    cB
    csh
    elspan.1
    elintrab
    syl6bb
end
