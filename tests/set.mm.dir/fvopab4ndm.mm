include "wcel.mm"
include "wn.mm"
include "cdm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "copab.mm"
include "dmeqi.mm"
include "dmopabss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"

theorem fvopab4ndm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  assume fvopab4ndm.1: |- F = { <. x , y >. | ( x e. A /\ ph ) }

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( -. B e. A -> ( F ` B ) = (/) )

  proof
    cB
    cA
    wcel
    #
    wn
    cB
    cF
    cdm
    #
    wcel
    #
    wn
    cB
    cF
    cfv
    c0
    wceq
    @2
    @0
    @1
    cA
    cB
    @1
    vx
    cv
    cA
    wcel
    wph
    wa
    vx
    vy
    copab
    #
    cdm
    cA
    cF
    @3
    fvopab4ndm.1
    dmeqi
    wph
    vx
    vy
    cA
    dmopabss
    eqsstri
    sseli
    con3i
    cB
    cF
    ndmfv
    syl
end
