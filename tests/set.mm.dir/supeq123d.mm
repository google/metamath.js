include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "cuni.mm"
include "csup.mm"
include "breqd.mm"
include "notbid.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "unieqd.mm"
include "df-sup.mm"
include "3eqtr4g.mm"

theorem supeq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume supeq123d.a: |- ( ph -> A = D )
  assume supeq123d.b: |- ( ph -> B = E )
  assume supeq123d.c: |- ( ph -> C = F )


  assert |- ( ph -> sup ( A , B , C ) = sup ( D , E , F ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cC
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @1
    @0
    cC
    wbr
    #
    @1
    vz
    cv
    #
    cC
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    crab
    #
    cuni
    @0
    @1
    cF
    wbr
    #
    wn
    #
    vy
    cD
    wral
    #
    @1
    @0
    cF
    wbr
    #
    @1
    @6
    cF
    wbr
    #
    vz
    cD
    wrex
    #
    wi
    #
    vy
    cE
    wral
    #
    wa
    #
    vx
    cE
    crab
    #
    cuni
    cA
    cB
    cC
    csup
    cD
    cE
    cF
    csup
    wph
    @12
    @22
    wph
    @11
    @21
    vx
    cB
    cE
    supeq123d.b
    wph
    @4
    @15
    @10
    @20
    wph
    @3
    @14
    vy
    cA
    cD
    supeq123d.a
    wph
    @2
    @13
    wph
    cC
    cF
    @0
    @1
    supeq123d.c
    breqd
    notbid
    raleqbidv
    wph
    @9
    @19
    vy
    cB
    cE
    supeq123d.b
    wph
    @5
    @16
    @8
    @18
    wph
    cC
    cF
    @1
    @0
    supeq123d.c
    breqd
    wph
    @7
    @17
    vz
    cA
    cD
    supeq123d.a
    wph
    cC
    cF
    @1
    @6
    supeq123d.c
    breqd
    rexeqbidv
    imbi12d
    raleqbidv
    anbi12d
    rabeqbidv
    unieqd
    vx
    vy
    vz
    cA
    cB
    cC
    df-sup
    vx
    vy
    vz
    cD
    cE
    cF
    df-sup
    3eqtr4g
end
