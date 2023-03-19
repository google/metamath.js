include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "dfral2.mm"
include "con2bii.mm"

theorem rexnal
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A -. ph <-> -. A. x e. A ph )

  proof
    wph
    vx
    cA
    wral
    wph
    wn
    vx
    cA
    wrex
    wph
    vx
    cA
    dfral2
    con2bii
end
