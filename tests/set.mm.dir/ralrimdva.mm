include "cv.mm"
include "wcel.mm"
include "expimpd.mm"
include "expcomd.mm"
include "ralrimdv.mm"

theorem ralrimdva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralrimdva.1: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )

  disjoint ph x
  disjoint ps x
  assert |- ( ph -> ( ps -> A. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wch
    wph
    @0
    wps
    wch
    ralrimdva.1
    expimpd
    expcomd
    ralrimdv
end
