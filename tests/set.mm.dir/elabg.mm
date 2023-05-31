include "nfcv.mm"
include "nfv.mm"
include "elabgf.mm"

theorem elabg
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  param cV: class V
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
