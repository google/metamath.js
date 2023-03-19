include "wrex.mm"
include "rspcedv.mm"
include "mpd.mm"

theorem rspcedvd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcedvd.1: |- ( ph -> A e. B )
  assume rspcedvd.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume rspcedvd.3: |- ( ph -> ch )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> E. x e. B ps )

  proof
    wph
    wch
    wps
    vx
    cB
    wrex
    rspcedvd.3
    wph
    wps
    wch
    vx
    cA
    cB
    rspcedvd.1
    rspcedvd.2
    rspcedv
    mpd
end
