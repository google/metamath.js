include "rspec.mm"
include "vtoclga.mm"

theorem vtoclri
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume vtoclri.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclri.2: |- A. x e. B ph

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
    vtoclri.1
    wph
    vx
    cB
    vtoclri.2
    rspec
    vtoclga
end
