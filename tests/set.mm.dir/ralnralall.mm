include "wral.mm"
include "wn.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "r19.26.mm"
include "wfal.mm"
include "pm3.24.mm"
include "bifal.mm"
include "ralbii.mm"
include "r19.3rzv.mm"
include "falim.mm"
include "syl6bir.mm"
include "syl5bi.mm"
include "syl5bir.mm"

theorem ralnralall
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) -> ( ( A. x e. A ph /\ A. x e. A -. ph ) -> ps ) )

  proof
    wph
    vx
    cA
    wral
    wph
    wn
    #
    vx
    cA
    wral
    wa
    wph
    @0
    wa
    #
    vx
    cA
    wral
    #
    cA
    c0
    wne
    #
    wps
    wph
    @0
    vx
    cA
    r19.26
    @2
    wfal
    vx
    cA
    wral
    #
    @3
    wps
    @1
    wfal
    vx
    cA
    @1
    wph
    pm3.24
    bifal
    ralbii
    @3
    @4
    wfal
    wps
    wfal
    vx
    cA
    r19.3rzv
    wps
    falim
    syl6bir
    syl5bi
    syl5bir
end
