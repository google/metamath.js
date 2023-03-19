include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "rneqi.mm"
include "rnoprab2.mm"

theorem rnmpt2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let wps: wff ps
  let cD: class D
  let wph: wff ph
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint F w
  disjoint ps z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  assert |- ran F = { z | E. x e. A E. y e. B z = C }

  proof
    cF
    crn
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    vz
    cv
    cC
    wceq
    #
    wa
    vx
    vy
    vz
    coprab
    #
    crn
    @0
    vy
    cB
    wrex
    vx
    cA
    wrex
    vz
    cab
    cF
    @1
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @1
    rngop.1
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    eqtri
    rneqi
    @0
    vx
    vy
    vz
    cA
    cB
    rnoprab2
    eqtri
end
