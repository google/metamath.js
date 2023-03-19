include "wsbc.mm"
include "wb.mm"
include "wcel.mm"
include "sbcbii.mm"
include "a1i.mm"

theorem sbcbiiOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcbiiOLD.1: |- ( ph <-> ps )


  assert |- ( A e. V -> ( [. A / x ]. ph <-> [. A / x ]. ps ) )

  proof
    wph
    vx
    cA
    wsbc
    wps
    vx
    cA
    wsbc
    wb
    cA
    cV
    wcel
    wph
    wps
    vx
    cA
    sbcbiiOLD.1
    sbcbii
    a1i
end
