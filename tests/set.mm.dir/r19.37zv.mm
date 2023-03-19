include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "r19.3rzv.mm"
include "imbi1d.mm"
include "r19.35.mm"
include "syl6rbbr.mm"

theorem r19.37zv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ph x
  assert |- ( A =/= (/) -> ( E. x e. A ( ph -> ps ) <-> ( ph -> E. x e. A ps ) ) )

  proof
    cA
    c0
    wne
    #
    wph
    wps
    vx
    cA
    wrex
    #
    wi
    wph
    vx
    cA
    wral
    #
    @1
    wi
    wph
    wps
    wi
    vx
    cA
    wrex
    @0
    wph
    @2
    @1
    wph
    vx
    cA
    r19.3rzv
    imbi1d
    wph
    wps
    vx
    cA
    r19.35
    syl6rbbr
end
