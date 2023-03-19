include "wreu.mm"
include "wa.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "weu.mm"
include "wex.mm"
include "df-reu.mm"
include "df-rex.mm"
include "anass.mm"
include "exbii.mm"
include "bitr4i.mm"
include "eupick.mm"
include "syl2anb.mm"
include "expd.mm"
include "3impia.mm"

theorem reupick3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( E! x e. A ph /\ E. x e. A ( ph /\ ps ) /\ x e. A ) -> ( ph -> ps ) )

  proof
    wph
    vx
    cA
    wreu
    #
    wph
    wps
    wa
    #
    vx
    cA
    wrex
    #
    vx
    cv
    cA
    wcel
    #
    wph
    wps
    wi
    @0
    @2
    wa
    @3
    wph
    wps
    @0
    @3
    wph
    wa
    #
    vx
    weu
    @4
    wps
    wa
    #
    vx
    wex
    #
    @4
    wps
    wi
    @2
    wph
    vx
    cA
    df-reu
    @2
    @3
    @1
    wa
    #
    vx
    wex
    @6
    @1
    vx
    cA
    df-rex
    @5
    @7
    vx
    @3
    wph
    wps
    anass
    exbii
    bitr4i
    @4
    wps
    vx
    eupick
    syl2anb
    expd
    3impia
end
