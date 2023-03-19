include "wcel.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "nfra1.mm"
include "wb.mm"
include "rsp.mm"
include "clel3g.mm"
include "syl6.mm"
include "imp.mm"
include "rexbida.mm"
include "rexcom4.mm"
include "syl6bb.mm"
include "r19.41v.mm"
include "exbii.mm"
include "exancom.mm"
include "bitri.mm"
include "eliun.mm"
include "eluniab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem dfiun2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  let vw: setvar w

  disjoint A y
  disjoint B y
  disjoint x y
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint C w
  disjoint C z
  disjoint w x
  disjoint x z
  assert |- ( A. x e. A B e. C -> U_ x e. A B = U. { y | E. x e. A y = B } )

  proof
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vz
    vx
    cA
    cB
    ciun
    #
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    cuni
    #
    @1
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @7
    @3
    wcel
    #
    @5
    wa
    vy
    wex
    #
    @7
    @2
    wcel
    @7
    @6
    wcel
    @1
    @9
    @4
    @10
    wa
    #
    vx
    cA
    wrex
    #
    vy
    wex
    #
    @11
    @1
    @9
    @12
    vy
    wex
    #
    vx
    cA
    wrex
    @14
    @1
    @8
    @15
    vx
    cA
    @0
    vx
    cA
    nfra1
    @1
    vx
    cv
    cA
    wcel
    #
    @8
    @15
    wb
    #
    @1
    @16
    @0
    @17
    @0
    vx
    cA
    rsp
    vy
    @7
    cB
    cC
    clel3g
    syl6
    imp
    rexbida
    @12
    vx
    vy
    cA
    rexcom4
    syl6bb
    @14
    @5
    @10
    wa
    #
    vy
    wex
    @11
    @13
    @18
    vy
    @4
    @10
    vx
    cA
    r19.41v
    exbii
    @5
    @10
    vy
    exancom
    bitri
    syl6bb
    vx
    @7
    cA
    cB
    eliun
    @5
    vy
    @7
    eluniab
    3bitr4g
    eqrdv
end
