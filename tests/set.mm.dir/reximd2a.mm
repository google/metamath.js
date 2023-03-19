include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "jca.mm"
include "expl.mm"
include "eximd.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "mpd.mm"

theorem reximd2a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume reximd2a.1: |- F/ x ph
  assume reximd2a.2: |- ( ( ( ph /\ x e. A ) /\ ps ) -> x e. B )
  assume reximd2a.3: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )
  assume reximd2a.4: |- ( ph -> E. x e. A ps )


  assert |- ( ph -> E. x e. B ch )

  proof
    wph
    wps
    vx
    cA
    wrex
    #
    wch
    vx
    cB
    wrex
    #
    reximd2a.4
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vx
    wex
    @2
    cB
    wcel
    #
    wch
    wa
    #
    vx
    wex
    @0
    @1
    wph
    @4
    @6
    vx
    reximd2a.1
    wph
    @3
    wps
    @6
    wph
    @3
    wa
    wps
    wa
    @5
    wch
    reximd2a.2
    reximd2a.3
    jca
    expl
    eximd
    wps
    vx
    cA
    df-rex
    wch
    vx
    cB
    df-rex
    3imtr4g
    mpd
end
