include "nfcv.mm"
include "nfv.mm"
include "elabgf.mm"

theorem elabg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume elabg.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( A e. V -> ( A e. { x | ph } <-> ps ) )

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
    elabg.1
    elabgf
end
