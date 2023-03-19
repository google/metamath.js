include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "fvexd.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem caonncan
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cI: class I
  let cM: class M
  let cV: class V
  let vz: setvar z
  assume caonncan.i: |- ( ph -> I e. V )
  assume caonncan.a: |- ( ph -> A : I --> S )
  assume caonncan.b: |- ( ph -> B : I --> S )
  assume caonncan.z: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x M ( x M y ) ) = y )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint S y
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint I z
  disjoint M z
  assert |- ( ph -> ( A oF M ( A oF M B ) ) = B )

  proof
    wph
    vz
    cI
    vz
    cv
    #
    cA
    cfv
    #
    @1
    @0
    cB
    cfv
    #
    cM
    co
    #
    cM
    co
    #
    cmpt
    vz
    cI
    @2
    cmpt
    cA
    cA
    cB
    cM
    cof
    #
    co
    #
    @5
    co
    cB
    wph
    vz
    cI
    @4
    @2
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @1
    cS
    wcel
    @2
    cS
    wcel
    vx
    cv
    #
    @9
    vy
    cv
    #
    cM
    co
    #
    cM
    co
    #
    @10
    wceq
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @4
    @2
    wceq
    #
    wph
    cI
    cS
    @0
    cA
    caonncan.a
    ffvelrnda
    wph
    cI
    cS
    @0
    cB
    caonncan.b
    ffvelrnda
    wph
    @14
    @7
    wph
    @13
    vx
    vy
    cS
    cS
    caonncan.z
    ralrimivva
    adantr
    @13
    @15
    @1
    @1
    @10
    cM
    co
    #
    cM
    co
    #
    @10
    wceq
    vx
    vy
    @1
    @2
    cS
    cS
    @9
    @1
    wceq
    #
    @12
    @17
    @10
    @18
    @9
    @1
    @11
    @16
    cM
    @18
    id
    @9
    @1
    @10
    cM
    oveq1
    oveq12d
    eqeq1d
    @10
    @2
    wceq
    #
    @17
    @4
    @10
    @2
    @19
    @16
    @3
    @1
    cM
    @10
    @2
    @1
    cM
    oveq2
    oveq2d
    @19
    id
    eqeq12d
    rspc2va
    syl21anc
    mpteq2dva
    wph
    vz
    cI
    @1
    @3
    cM
    cA
    @6
    cV
    cvv
    cvv
    caonncan.i
    @8
    @0
    cA
    fvexd
    #
    @8
    @1
    @2
    cM
    ovexd
    wph
    vz
    cI
    cS
    cA
    caonncan.a
    feqmptd
    #
    wph
    vz
    cI
    @1
    @2
    cM
    cA
    cB
    cV
    cvv
    cvv
    caonncan.i
    @20
    @8
    @0
    cB
    fvexd
    @21
    wph
    vz
    cI
    cS
    cB
    caonncan.b
    feqmptd
    #
    offval2
    offval2
    @22
    3eqtr4d
end
