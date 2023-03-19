include "wss.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "id.mm"
include "rgenw.mm"
include "reuss2.mm"
include "mpanl2.mm"
include "3impb.mm"

theorem reuss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) -> E! x e. A ph )

  proof
    cA
    cB
    wss
    #
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cB
    wreu
    #
    wph
    vx
    cA
    wreu
    #
    @0
    wph
    wph
    wi
    #
    vx
    cA
    wral
    @1
    @2
    wa
    @3
    @4
    vx
    cA
    wph
    id
    rgenw
    wph
    wph
    vx
    cA
    cB
    reuss2
    mpanl2
    3impb
end
