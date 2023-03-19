include "wceq.mm"
include "wsbc.mm"
include "dfsbcq.mm"
include "biimpd.mm"

theorem axfrege52c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) )

  proof
    cA
    cB
    wceq
    wph
    vx
    cA
    wsbc
    wph
    vx
    cB
    wsbc
    wph
    vx
    cA
    cB
    dfsbcq
    biimpd
end
