include "wral.mm"
include "wa.mm"
include "nfra1.mm"
include "nfan.mm"
include "cv.mm"
include "wcel.mm"
include "id.mm"
include "adantlr.mm"
include "rspa.mm"
include "adantll.mm"
include "sylc.mm"
include "ralrimia.mm"
include "ex.mm"

theorem ralimda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralimda.1: |- F/ x ph
  assume ralimda.2: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )


  assert |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) )

  proof
    wph
    wps
    vx
    cA
    wral
    #
    wch
    vx
    cA
    wral
    wph
    @0
    wa
    #
    wch
    vx
    cA
    wph
    @0
    vx
    ralimda.1
    wps
    vx
    cA
    nfra1
    nfan
    @1
    vx
    cv
    cA
    wcel
    #
    wa
    wph
    @2
    wa
    #
    wps
    wch
    wph
    @2
    @3
    @0
    @3
    id
    adantlr
    @0
    @2
    wps
    wph
    wps
    vx
    cA
    rspa
    adantll
    ralimda.2
    sylc
    ralrimia
    ex
end
