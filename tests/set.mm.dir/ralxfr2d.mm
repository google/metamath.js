include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "syl.mm"
include "wi.mm"
include "wrex.mm"
include "wral.mm"
include "biimprd.mm"
include "r19.23v.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "eleq1.mm"
include "mpbidi.mm"
include "exlimdv.mm"
include "mpd.mm"
include "biimpa.mm"
include "ralxfrd.mm"

theorem ralxfr2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume ralxfr2d.1: |- ( ( ph /\ y e. C ) -> A e. V )
  assume ralxfr2d.2: |- ( ph -> ( x e. B <-> E. y e. C x = A ) )
  assume ralxfr2d.3: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint ch x
  disjoint ph x
  disjoint ph y
  disjoint ps y
  assert |- ( ph -> ( A. x e. B ps <-> A. y e. C ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    wph
    vy
    cv
    cC
    wcel
    wa
    #
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    cA
    cB
    wcel
    #
    @0
    cA
    cV
    wcel
    @3
    ralxfr2d.1
    vx
    cA
    cV
    elisset
    syl
    @0
    @2
    @4
    vx
    @2
    @1
    cB
    wcel
    #
    @4
    @0
    wph
    @2
    @5
    wi
    #
    vy
    cC
    wph
    @2
    vy
    cC
    wrex
    #
    @5
    wi
    @6
    vy
    cC
    wral
    wph
    @5
    @7
    ralxfr2d.2
    biimprd
    @2
    @5
    vy
    cC
    r19.23v
    sylibr
    r19.21bi
    @1
    cA
    cB
    eleq1
    mpbidi
    exlimdv
    mpd
    wph
    @5
    @7
    ralxfr2d.2
    biimpa
    ralxfr2d.3
    ralxfrd
end
