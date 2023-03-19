include "wb.mm"
include "cv.mm"
include "wceq.mm"
include "bibi12d.mm"
include "vtocl.mm"

theorem vtoclb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  assume vtoclb.1: |- A e. _V
  assume vtoclb.2: |- ( x = A -> ( ph <-> ch ) )
  assume vtoclb.3: |- ( x = A -> ( ps <-> th ) )
  assume vtoclb.4: |- ( ph <-> ps )

  disjoint A x
  disjoint ch x
  disjoint th x
  assert |- ( ch <-> th )

  proof
    wph
    wps
    wb
    wch
    wth
    wb
    vx
    cA
    vtoclb.1
    vx
    cv
    cA
    wceq
    wph
    wch
    wps
    wth
    vtoclb.2
    vtoclb.3
    bibi12d
    vtoclb.4
    vtocl
end
