include "nfcv.mm"
include "nfv.mm"
include "elrabf.mm"

theorem elrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elrab.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  disjoint B x
  assert |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) )

  proof
    wph
    wps
    vx
    cA
    cB
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    wps
    vx
    nfv
    elrab.1
    elrabf
end
