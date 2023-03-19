include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "raaanv.mm"
include "prth.mm"
include "eqtr2.mm"
include "syl6.mm"
include "2ralimi.mm"
include "sylbir.mm"
include "mpdan.mm"
include "rexlimivw.mm"

theorem reusv3i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume reusv3.1: |- ( y = z -> ( ph <-> ps ) )
  assume reusv3.2: |- ( y = z -> C = D )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph z
  disjoint ps x
  disjoint ps y
  assert |- ( E. x e. A A. y e. B ( ph -> x = C ) -> A. y e. B A. z e. B ( ( ph /\ ps ) -> C = D ) )

  proof
    wph
    vx
    cv
    #
    cC
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    wph
    wps
    wa
    #
    cC
    cD
    wceq
    #
    wi
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    vx
    cA
    @3
    wps
    @0
    cD
    wceq
    #
    wi
    #
    vz
    cB
    wral
    #
    @7
    @3
    @10
    @2
    @9
    vy
    vz
    cB
    vy
    cv
    vz
    cv
    wceq
    #
    wph
    wps
    @1
    @8
    reusv3.1
    @11
    cC
    cD
    @0
    reusv3.2
    eqeq2d
    imbi12d
    cbvralv
    biimpi
    @3
    @10
    wa
    @2
    @9
    wa
    #
    vz
    cB
    wral
    vy
    cB
    wral
    @7
    @2
    @9
    vy
    vz
    cB
    raaanv
    @12
    @6
    vy
    vz
    cB
    cB
    @12
    @4
    @1
    @8
    wa
    @5
    wph
    @1
    wps
    @8
    prth
    @0
    cC
    cD
    eqtr2
    syl6
    2ralimi
    sylbir
    mpdan
    rexlimivw
end
