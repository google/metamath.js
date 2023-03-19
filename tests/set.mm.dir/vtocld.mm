include "nfv.mm"
include "nfcvd.mm"
include "nfvd.mm"
include "vtocldf.mm"

theorem vtocld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtocld.1: |- ( ph -> A e. V )
  assume vtocld.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume vtocld.3: |- ( ph -> ps )

  disjoint A x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    vx
    cA
    cV
    vtocld.1
    vtocld.2
    vtocld.3
    wph
    vx
    nfv
    wph
    vx
    cA
    nfcvd
    wph
    wch
    vx
    nfvd
    vtocldf
end
