include "wb.mm"
include "cv.mm"
include "wceq.mm"
include "bibi12d.mm"
include "vtoclg.mm"

theorem vtoclbg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtoclbg.1: |- ( x = A -> ( ph <-> ch ) )
  assume vtoclbg.2: |- ( x = A -> ( ps <-> th ) )
  assume vtoclbg.3: |- ( ph <-> ps )

  disjoint A x
  disjoint ch x
  disjoint th x
  assert |- ( A e. V -> ( ch <-> th ) )

  proof
    wph
    wps
    wb
    wch
    wth
    wb
    vx
    cA
    cV
    vx
    cv
    cA
    wceq
    wph
    wch
    wps
    wth
    vtoclbg.1
    vtoclbg.2
    bibi12d
    vtoclbg.3
    vtoclg
end
