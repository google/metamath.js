include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "biimpd.mm"
include "spcimdv.mm"

theorem spcdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume spcimdv.1: |- ( ph -> A e. B )
  assume spcdv.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( A. x ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    cB
    spcimdv.1
    wph
    vx
    cv
    cA
    wceq
    wa
    wps
    wch
    spcdv.2
    biimpd
    spcimdv
end
