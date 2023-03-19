include "wceq.mm"
include "wsbc.mm"
include "wb.mm"
include "dfsbcq.mm"
include "syl.mm"

theorem sbceq1d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume sbceq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( [. A / x ]. ps <-> [. B / x ]. ps ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    vx
    cA
    wsbc
    wps
    vx
    cB
    wsbc
    wb
    sbceq1d.1
    wps
    vx
    cA
    cB
    dfsbcq
    syl
end
