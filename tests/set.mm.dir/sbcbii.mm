include "wsbc.mm"
include "wb.mm"
include "wtru.mm"
include "a1i.mm"
include "sbcbidv.mm"
include "trud.mm"

theorem sbcbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume sbcbii.1: |- ( ph <-> ps )


  assert |- ( [. A / x ]. ph <-> [. A / x ]. ps )

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
    wtru
    wph
    wps
    vx
    cA
    wph
    wps
    wb
    wtru
    sbcbii.1
    a1i
    sbcbidv
    trud
end
