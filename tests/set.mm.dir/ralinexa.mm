include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "imnan.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"

theorem ralinexa
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph -> -. ps ) <-> -. E. x e. A ( ph /\ ps ) )

  proof
    wph
    wps
    wn
    wi
    #
    vx
    cA
    wral
    wph
    wps
    wa
    #
    wn
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wrex
    wn
    @0
    @2
    vx
    cA
    wph
    wps
    imnan
    ralbii
    @1
    vx
    cA
    ralnex
    bitri
end
