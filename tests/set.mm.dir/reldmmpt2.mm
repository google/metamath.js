include "cdm.mm"
include "wrel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "reldmoprab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "releqi.mm"
include "mpbir.mm"

theorem reldmmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let wps: wff ps
  let cD: class D
  let wph: wff ph
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A y
  disjoint x y
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
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  assert |- Rel dom F

  proof
    cF
    cdm
    #
    wrel
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
    wa
    #
    vx
    vy
    vz
    coprab
    #
    cdm
    #
    wrel
    @1
    vx
    vy
    vz
    reldmoprab
    @0
    @3
    cF
    @2
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @2
    rngop.1
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    eqtri
    dmeqi
    releqi
    mpbir
end
