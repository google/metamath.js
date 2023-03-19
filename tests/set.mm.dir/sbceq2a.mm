include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "wb.mm"
include "sbceq1a.mm"
include "eqcoms.mm"
include "bicomd.mm"

theorem sbceq2a
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A = x -> ( [. A / x ]. ph <-> ph ) )

  proof
    cA
    vx
    cv
    #
    wceq
    wph
    wph
    vx
    cA
    wsbc
    #
    wph
    @1
    wb
    @0
    cA
    wph
    vx
    cA
    sbceq1a
    eqcoms
    bicomd
end
