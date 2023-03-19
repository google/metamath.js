include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "wrex.mm"
include "r19.9rzv.mm"
include "imbi2d.mm"
include "r19.35.mm"
include "syl6rbbr.mm"

theorem r19.36zv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ps x
  assert |- ( A =/= (/) -> ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> ps ) ) )

  proof
    cA
    c0
    wne
    #
    wph
    vx
    cA
    wral
    #
    wps
    wi
    @1
    wps
    vx
    cA
    wrex
    #
    wi
    wph
    wps
    wi
    vx
    cA
    wrex
    @0
    wps
    @2
    @1
    wps
    vx
    cA
    r19.9rzv
    imbi2d
    wph
    wps
    vx
    cA
    r19.35
    syl6rbbr
end
