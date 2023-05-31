include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "ralnex.mm"
include "con2bii.mm"

theorem dfrex2
  param wph: wff ph
  param vx: setvar x
  param cA: class A


  assert |- ( E. x e. A ph <-> -. A. x e. A -. ph )

  proof
    wph
    wn
    vx
    cA
    wral
    wph
    vx
    cA
    wrex
    wph
    vx
    cA
    ralnex
    con2bii
end
