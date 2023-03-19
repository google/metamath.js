include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "biimpd.mm"
include "rspcimdv.mm"

theorem rspcdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcdv.1: |- ( ph -> A e. B )
  assume rspcdv.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( A. x e. B ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    cB
    rspcdv.1
    wph
    vx
    cv
    cA
    wceq
    wa
    wps
    wch
    rspcdv.2
    biimpd
    rspcimdv
end
