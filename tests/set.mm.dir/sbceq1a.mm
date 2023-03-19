include "wsb.mm"
include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "sbid.mm"
include "dfsbcq2.mm"
include "syl5bbr.mm"

theorem sbceq1a
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( x = A -> ( ph <-> [. A / x ]. ph ) )

  proof
    wph
    wph
    vx
    vx
    wsb
    vx
    cv
    cA
    wceq
    wph
    vx
    cA
    wsbc
    wph
    vx
    sbid
    wph
    vx
    vx
    cA
    dfsbcq2
    syl5bbr
end
