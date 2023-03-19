include "wtru.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "nfcv.mm"
include "nftru.mm"
include "wceq.mm"
include "biidd.mm"
include "elrabf.mm"
include "tru.mm"
include "biantru.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem rabtru
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume rabtru.1: |- F/_ x A


  assert |- { x e. A | T. } = A

  proof
    vy
    wtru
    vx
    cA
    crab
    #
    cA
    vy
    cv
    #
    @0
    wcel
    @1
    cA
    wcel
    #
    wtru
    wa
    @2
    wtru
    wtru
    vx
    @1
    cA
    vx
    @1
    nfcv
    rabtru.1
    vx
    nftru
    vx
    cv
    @1
    wceq
    wtru
    biidd
    elrabf
    wtru
    @2
    tru
    biantru
    bitr4i
    eqriv
end
