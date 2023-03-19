include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "coprab.mm"
include "cvv.mm"
include "wfun.mm"
include "cdm.mm"
include "wmo.mm"
include "wi.mm"
include "moanimv.mm"
include "mpbir.mm"
include "funoprab.mm"
include "cxp.mm"
include "xpex.mm"
include "dmoprabss.mm"
include "ssexi.mm"
include "funex.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem oprabex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  assume oprabex.1: |- A e. _V
  assume oprabex.2: |- B e. _V
  assume oprabex.3: |- ( ( x e. A /\ y e. B ) -> E* z ph )
  assume oprabex.4: |- F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) }

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- F e. _V

  proof
    cF
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    wph
    wa
    #
    vx
    vy
    vz
    coprab
    #
    cvv
    oprabex.4
    @2
    wfun
    @2
    cdm
    #
    cvv
    wcel
    @2
    cvv
    wcel
    @1
    vx
    vy
    vz
    @1
    vz
    wmo
    @0
    wph
    vz
    wmo
    wi
    oprabex.3
    @0
    wph
    vz
    moanimv
    mpbir
    funoprab
    @3
    cA
    cB
    cxp
    cA
    cB
    oprabex.1
    oprabex.2
    xpex
    wph
    vx
    vy
    vz
    cA
    cB
    dmoprabss
    ssexi
    cvv
    @2
    funex
    mp2an
    eqeltri
end
