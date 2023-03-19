include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt2.mm"
include "eleq2i.mm"
include "cvv.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab3.mm"
include "bitri.mm"

theorem elrnmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let wps: wff ps
  let wph: wff ph
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )
  assume elrnmpt2.1: |- C e. _V

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
  assert |- ( D e. ran F <-> E. x e. A E. y e. B D = C )

  proof
    cD
    cF
    crn
    #
    wcel
    cD
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
    #
    vz
    cab
    #
    wcel
    cD
    cC
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @0
    @4
    cD
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    rngop.1
    rnmpt2
    eleq2i
    @3
    @7
    vz
    cD
    @6
    cD
    cvv
    wcel
    #
    vx
    cA
    @5
    @8
    vy
    cB
    @5
    @8
    cC
    cvv
    wcel
    elrnmpt2.1
    cD
    cC
    cvv
    eleq1
    mpbiri
    rexlimivw
    rexlimivw
    @1
    cD
    wceq
    @2
    @5
    vx
    vy
    cA
    cB
    @1
    cD
    cC
    eqeq1
    2rexbidv
    elab3
    bitri
end
