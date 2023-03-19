include "sbcbii.mm"

theorem bnj524
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj524.1: |- ( ph <-> ps )
  assume bnj524.2: |- A e. _V


  assert |- ( [. A / x ]. ph <-> [. A / x ]. ps )

  proof
    wph
    wps
    vx
    cA
    bnj524.1
    sbcbii
end
