include "wral.mm"
include "rspcdv.mm"
include "mpd.mm"

theorem rspcdvinvd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcdvinvd.1: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume rspcdvinvd.2: |- ( ph -> A e. B )
  assume rspcdvinvd.3: |- ( ph -> A. x e. B ps )

  disjoint A x
  disjoint B x
  disjoint ch x
  disjoint ph x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    cB
    wral
    wch
    rspcdvinvd.3
    wph
    wps
    wch
    vx
    cA
    cB
    rspcdvinvd.2
    rspcdvinvd.1
    rspcdv
    mpd
end
