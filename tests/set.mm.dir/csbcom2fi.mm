include "csb.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "df-csb.mm"
include "abeq2i.mm"
include "sbcbii.mm"
include "bitri.mm"
include "eleq2i.mm"
include "bitr3i.mm"
include "sbccom2fi.mm"
include "sbcel2.mm"
include "3bitri.mm"
include "eqriv.mm"

theorem csbcom2fi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vz: setvar z
  assume csbcom2fi.1: |- A e. _V
  assume csbcom2fi.2: |- F/_ y A
  assume csbcom2fi.3: |- [_ A / x ]_ B = C
  assume csbcom2fi.4: |- [_ A / x ]_ D = E

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint E z
  assert |- [_ A / x ]_ [_ B / y ]_ D = [_ C / y ]_ E

  proof
    vz
    vx
    cA
    vy
    cB
    cD
    csb
    #
    csb
    #
    vy
    cC
    cE
    csb
    #
    vz
    cv
    #
    @1
    wcel
    #
    @3
    cD
    wcel
    #
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    @3
    cE
    wcel
    #
    vy
    cC
    wsbc
    @3
    @2
    wcel
    @4
    @3
    @0
    wcel
    #
    vx
    cA
    wsbc
    #
    @7
    @10
    vz
    @1
    vx
    vz
    cA
    @0
    df-csb
    abeq2i
    @9
    @6
    vx
    cA
    @6
    vz
    @0
    vy
    vz
    cB
    cD
    df-csb
    abeq2i
    sbcbii
    bitri
    @5
    @8
    vx
    vy
    cA
    cB
    cC
    csbcom2fi.1
    csbcom2fi.2
    csbcom2fi.3
    @5
    vx
    cA
    wsbc
    #
    @3
    vx
    cA
    cD
    csb
    #
    wcel
    @8
    @11
    vz
    @12
    vx
    vz
    cA
    cD
    df-csb
    abeq2i
    @12
    cE
    @3
    csbcom2fi.4
    eleq2i
    bitr3i
    sbccom2fi
    vy
    cC
    @3
    cE
    sbcel2
    3bitri
    eqriv
end
