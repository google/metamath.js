include "cun.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "ssun1.mm"
include "orc.mm"
include "rgenw.mm"
include "reuss2.mm"
include "mpanl12.mm"

theorem reuun1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( E. x e. A ph /\ E! x e. ( A u. B ) ( ph \/ ps ) ) -> E! x e. A ph )

  proof
    cA
    cA
    cB
    cun
    #
    wss
    wph
    wph
    wps
    wo
    #
    wi
    #
    vx
    cA
    wral
    wph
    vx
    cA
    wrex
    @1
    vx
    @0
    wreu
    wa
    wph
    vx
    cA
    wreu
    cA
    cB
    ssun1
    @2
    vx
    cA
    wph
    wps
    orc
    rgenw
    wph
    @1
    vx
    cA
    @0
    reuss2
    mpanl12
end
