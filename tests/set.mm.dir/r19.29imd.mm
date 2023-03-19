include "wi.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "r19.29r.mm"
include "syl2anc.mm"
include "abai.mm"
include "rexbii.mm"
include "sylibr.mm"

theorem r19.29imd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume r19.29imd.1: |- ( ph -> E. x e. A ps )
  assume r19.29imd.2: |- ( ph -> A. x e. A ( ps -> ch ) )


  assert |- ( ph -> E. x e. A ( ps /\ ch ) )

  proof
    wph
    wps
    wps
    wch
    wi
    #
    wa
    #
    vx
    cA
    wrex
    #
    wps
    wch
    wa
    #
    vx
    cA
    wrex
    wph
    wps
    vx
    cA
    wrex
    @0
    vx
    cA
    wral
    @2
    r19.29imd.1
    r19.29imd.2
    wps
    @0
    vx
    cA
    r19.29r
    syl2anc
    @3
    @1
    vx
    cA
    wps
    wch
    abai
    rexbii
    sylibr
end
