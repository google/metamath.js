include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "3simpa.mm"
include "cv.mm"
include "wb.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "3adant3.mm"
include "anbi12d.mm"
include "wmo.mm"
include "wi.mm"
include "moanimv.mm"
include "mpbir.mm"
include "ovigg.mm"
include "mpand.mm"

theorem ovig
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  assume ovig.1: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )
  assume ovig.2: |- ( ( x e. R /\ y e. S ) -> E* z ph )
  assume ovig.3: |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) }

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
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( ( A e. R /\ B e. S /\ C e. D ) -> ( ps -> ( A F B ) = C ) )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cD
    wcel
    #
    w3a
    @0
    @1
    wa
    #
    wps
    cA
    cB
    cF
    co
    cC
    wceq
    @0
    @1
    @2
    3simpa
    vx
    cv
    #
    cR
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    #
    wph
    wa
    #
    @3
    wps
    wa
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    cR
    cS
    cD
    @4
    cA
    wceq
    #
    @6
    cB
    wceq
    #
    vz
    cv
    cC
    wceq
    #
    w3a
    @8
    @3
    wph
    wps
    @10
    @11
    @8
    @3
    wb
    @12
    @10
    @5
    @0
    @11
    @7
    @1
    @4
    cA
    cR
    eleq1
    @6
    cB
    cS
    eleq1
    bi2anan9
    3adant3
    ovig.1
    anbi12d
    @9
    vz
    wmo
    @8
    wph
    vz
    wmo
    wi
    ovig.2
    @8
    wph
    vz
    moanimv
    mpbir
    ovig.3
    ovigg
    mpand
end
