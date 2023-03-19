include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "affineequiv.mm"
include "subcld.mm"
include "mulcld.mm"
include "subcanad.mm"
include "nnncan1d.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "eqeq12d.mm"
include "3bitr2d.mm"

theorem affineequiv2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume affineequiv.A: |- ( ph -> A e. CC )
  assume affineequiv.B: |- ( ph -> B e. CC )
  assume affineequiv.C: |- ( ph -> C e. CC )
  assume affineequiv.D: |- ( ph -> D e. CC )


  assert |- ( ph -> ( B = ( ( D x. A ) + ( ( 1 - D ) x. C ) ) <-> ( B - A ) = ( ( 1 - D ) x. ( C - A ) ) ) )

  proof
    wph
    cB
    cD
    cA
    cmul
    co
    c1
    cD
    cmin
    co
    #
    cC
    cmul
    co
    caddc
    co
    wceq
    cC
    cB
    cmin
    co
    #
    cD
    cC
    cA
    cmin
    co
    #
    cmul
    co
    #
    wceq
    @2
    @1
    cmin
    co
    #
    @2
    @3
    cmin
    co
    #
    wceq
    cB
    cA
    cmin
    co
    #
    @0
    @2
    cmul
    co
    #
    wceq
    wph
    cA
    cB
    cC
    cD
    affineequiv.A
    affineequiv.B
    affineequiv.C
    affineequiv.D
    affineequiv
    wph
    @2
    @1
    @3
    wph
    cC
    cA
    affineequiv.C
    affineequiv.A
    subcld
    #
    wph
    cC
    cB
    affineequiv.C
    affineequiv.B
    subcld
    wph
    cD
    @2
    affineequiv.D
    @8
    mulcld
    subcanad
    wph
    @4
    @6
    @5
    @7
    wph
    cC
    cA
    cB
    affineequiv.C
    affineequiv.A
    affineequiv.B
    nnncan1d
    wph
    @7
    c1
    @2
    cmul
    co
    #
    @3
    cmin
    co
    @5
    wph
    c1
    cD
    @2
    wph
    1cnd
    affineequiv.D
    @8
    subdird
    wph
    @9
    @2
    @3
    cmin
    wph
    @2
    @8
    mulid2d
    oveq1d
    eqtr2d
    eqeq12d
    3bitr2d
end
