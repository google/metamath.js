include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "rnmpt2.mm"
include "elab2g.mm"

theorem elrnmpt2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let vw: setvar w
  let vz: setvar z
  let wps: wff ps
  let wph: wff ph
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A y
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint F w
  disjoint F z
  disjoint ps z
  disjoint x z
  disjoint D z
  disjoint ph x
  disjoint ph y
  assert |- ( D e. V -> ( D e. ran F <-> E. x e. A E. y e. B D = C ) )

  proof
    vz
    cv
    #
    cC
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    cD
    cC
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    vz
    cD
    cF
    crn
    cV
    @0
    cD
    wceq
    @1
    @2
    vx
    vy
    cA
    cB
    @0
    cD
    cC
    eqeq1
    2rexbidv
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    rngop.1
    rnmpt2
    elab2g
end
