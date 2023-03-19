include "nfcv.mm"
include "nfv.mm"
include "vtoclgaf.mm"

theorem vtoclga
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume vtoclga.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclga.2: |- ( x e. B -> ph )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( A e. B -> ps )

  proof
    wph
    wps
    vx
    cA
    cB
    vx
    cA
    nfcv
    wps
    vx
    nfv
    vtoclga.1
    vtoclga.2
    vtoclgaf
end
