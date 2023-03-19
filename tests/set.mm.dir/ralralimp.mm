include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wo.mm"
include "wi.mm"
include "wn.mm"
include "wral.mm"
include "ornld.mm"
include "adantr.mm"
include "ralimdv.mm"
include "rspn0.mm"
include "adantl.mm"
include "syld.mm"

theorem ralralimp
  let wph: wff ph
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let cA: class A
  let vk: setvar k

  disjoint A x
  disjoint ph x
  disjoint ta x
  disjoint k x
  assert |- ( ( ph /\ A =/= (/) ) -> ( A. x e. A ( ( ph -> ( th \/ ta ) ) /\ -. th ) -> ta ) )

  proof
    wph
    cA
    c0
    wne
    #
    wa
    #
    wph
    wth
    wta
    wo
    wi
    wth
    wn
    wa
    #
    vx
    cA
    wral
    wta
    vx
    cA
    wral
    #
    wta
    @1
    @2
    wta
    vx
    cA
    wph
    @2
    wta
    wi
    @0
    wph
    wth
    wta
    ornld
    adantr
    ralimdv
    @0
    @3
    wta
    wi
    wph
    wta
    vx
    cA
    rspn0
    adantl
    syld
end
