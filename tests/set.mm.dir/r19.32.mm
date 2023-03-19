include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wo.mm"
include "nfn.mm"
include "r19.21.mm"
include "df-or.mm"
include "ralbii.mm"
include "3bitr4i.mm"

theorem r19.32
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume r19.32.1: |- F/ x ph


  assert |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) )

  proof
    wph
    wn
    #
    wps
    wi
    #
    vx
    cA
    wral
    @0
    wps
    vx
    cA
    wral
    #
    wi
    wph
    wps
    wo
    #
    vx
    cA
    wral
    wph
    @2
    wo
    @0
    wps
    vx
    cA
    wph
    vx
    r19.32.1
    nfn
    r19.21
    @3
    @1
    vx
    cA
    wph
    wps
    df-or
    ralbii
    wph
    @2
    df-or
    3bitr4i
end
