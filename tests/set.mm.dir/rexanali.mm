include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "dfrex2.mm"
include "iman.mm"
include "ralbii.mm"
include "xchbinxr.mm"

theorem rexanali
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ( ph /\ -. ps ) <-> -. A. x e. A ( ph -> ps ) )

  proof
    wph
    wps
    wn
    wa
    #
    vx
    cA
    wrex
    @0
    wn
    #
    vx
    cA
    wral
    wph
    wps
    wi
    #
    vx
    cA
    wral
    @0
    vx
    cA
    dfrex2
    @2
    @1
    vx
    cA
    wph
    wps
    iman
    ralbii
    xchbinxr
end
