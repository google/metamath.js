include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "notnotb.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"

theorem dfral2
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ph <-> -. E. x e. A -. ph )

  proof
    wph
    vx
    cA
    wral
    wph
    wn
    #
    wn
    #
    vx
    cA
    wral
    @0
    vx
    cA
    wrex
    wn
    wph
    @1
    vx
    cA
    wph
    notnotb
    ralbii
    @0
    vx
    cA
    ralnex
    bitri
end
