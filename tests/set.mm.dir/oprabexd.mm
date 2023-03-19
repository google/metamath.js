include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "coprab.mm"
include "cvv.mm"
include "wfun.mm"
include "cdm.mm"
include "wmo.mm"
include "wal.mm"
include "wi.mm"
include "ex.mm"
include "moanimv.mm"
include "sylibr.mm"
include "alrimivv.mm"
include "funoprabg.mm"
include "syl.mm"
include "cxp.mm"
include "wss.mm"
include "dmoprabss.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "sylancr.mm"
include "funex.mm"
include "eqeltrd.mm"

theorem oprabexd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  assume oprabexd.1: |- ( ph -> A e. _V )
  assume oprabexd.2: |- ( ph -> B e. _V )
  assume oprabexd.3: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> E* z ps )
  assume oprabexd.4: |- ( ph -> F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> F e. _V )

  proof
    wph
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
    wps
    wa
    #
    vx
    vy
    vz
    coprab
    #
    cvv
    oprabexd.4
    wph
    @2
    wfun
    #
    @2
    cdm
    #
    cvv
    wcel
    #
    @2
    cvv
    wcel
    wph
    @1
    vz
    wmo
    #
    vy
    wal
    vx
    wal
    @3
    wph
    @6
    vx
    vy
    wph
    @0
    wps
    vz
    wmo
    #
    wi
    @6
    wph
    @0
    @7
    oprabexd.3
    ex
    @0
    wps
    vz
    moanimv
    sylibr
    alrimivv
    @1
    vx
    vy
    vz
    funoprabg
    syl
    wph
    @4
    cA
    cB
    cxp
    #
    wss
    @8
    cvv
    wcel
    #
    @5
    wps
    vx
    vy
    vz
    cA
    cB
    dmoprabss
    wph
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @9
    oprabexd.1
    oprabexd.2
    cA
    cB
    cvv
    cvv
    xpexg
    syl2anc
    @4
    @8
    cvv
    ssexg
    sylancr
    cvv
    @2
    funex
    syl2anc
    eqeltrd
end
