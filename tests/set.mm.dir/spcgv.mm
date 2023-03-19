include "nfcv.mm"
include "nfv.mm"
include "spcgf.mm"

theorem spcgv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume spcgv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( A e. V -> ( A. x ph -> ps ) )

  proof
    wph
    wps
    vx
    cA
    cV
    vx
    cA
    nfcv
    wps
    vx
    nfv
    spcgv.1
    spcgf
end
