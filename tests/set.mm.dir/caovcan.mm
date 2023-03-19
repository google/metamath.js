include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi1d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "wcel.mm"
include "wa.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "vtocl.mm"
include "vtocl2ga.mm"

theorem caovcan
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cD: class D
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cT: class T
  assume caovcan.1: |- C e. _V
  assume caovcan.2: |- ( ( x e. S /\ y e. S ) -> ( ( x F y ) = ( x F z ) -> y = z ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( A e. S /\ B e. S ) -> ( ( A F B ) = ( A F C ) -> B = C ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    @0
    cC
    cF
    co
    #
    wceq
    #
    @1
    cC
    wceq
    #
    wi
    #
    cA
    @1
    cF
    co
    #
    cA
    cC
    cF
    co
    #
    wceq
    #
    @5
    wi
    cA
    cB
    cF
    co
    #
    @8
    wceq
    #
    cB
    cC
    wceq
    #
    wi
    vx
    vy
    cA
    cB
    cS
    cS
    @0
    cA
    wceq
    #
    @4
    @9
    @5
    @13
    @2
    @7
    @3
    @8
    @0
    cA
    @1
    cF
    oveq1
    @0
    cA
    cC
    cF
    oveq1
    eqeq12d
    imbi1d
    @1
    cB
    wceq
    #
    @9
    @11
    @5
    @12
    @14
    @7
    @10
    @8
    @1
    cB
    cA
    cF
    oveq2
    eqeq1d
    @1
    cB
    cC
    eqeq1
    imbi12d
    @0
    cS
    wcel
    @1
    cS
    wcel
    wa
    #
    @2
    @0
    vz
    cv
    #
    cF
    co
    #
    wceq
    #
    @1
    @16
    wceq
    #
    wi
    #
    wi
    @15
    @6
    wi
    vz
    cC
    caovcan.1
    @16
    cC
    wceq
    #
    @20
    @6
    @15
    @21
    @18
    @4
    @19
    @5
    @21
    @17
    @3
    @2
    @16
    cC
    @0
    cF
    oveq2
    eqeq2d
    @16
    cC
    @1
    eqeq2
    imbi12d
    imbi2d
    caovcan.2
    vtocl
    vtocl2ga
end
