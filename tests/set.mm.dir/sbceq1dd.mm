include "wsbc.mm"
include "sbceq1d.mm"
include "mpbid.mm"

theorem sbceq1dd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume sbceq1d.1: |- ( ph -> A = B )
  assume sbceq1dd.2: |- ( ph -> [. A / x ]. ps )


  assert |- ( ph -> [. B / x ]. ps )

  proof
    wph
    wps
    vx
    cA
    wsbc
    wps
    vx
    cB
    wsbc
    sbceq1dd.2
    wph
    wps
    vx
    cA
    cB
    sbceq1d.1
    sbceq1d
    mpbid
end
