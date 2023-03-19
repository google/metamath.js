include "nfcv.mm"
include "nfv.mm"
include "spcegf.mm"

theorem spcegv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume spcgv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( A e. V -> ( ps -> E. x ph ) )

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
    spcegf
end
