include "wss.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "crio.mm"
include "wceq.mm"
include "w3a.mm"
include "ssrexv.mm"
include "imp.mm"
include "3adant3.mm"
include "simp3.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riotass.mm"
include "syld3an3.mm"

theorem moriotass
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ B /\ E. x e. A ph /\ E* x e. B ph ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ph ) )

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
    wrmo
    #
    wph
    vx
    cB
    wreu
    #
    wph
    vx
    cA
    crio
    wph
    vx
    cB
    crio
    wceq
    @0
    @1
    @2
    w3a
    wph
    vx
    cB
    wrex
    #
    @2
    @3
    @0
    @1
    @4
    @2
    @0
    @1
    @4
    wph
    vx
    cA
    cB
    ssrexv
    imp
    3adant3
    @0
    @1
    @2
    simp3
    wph
    vx
    cB
    reu5
    sylanbrc
    wph
    vx
    cA
    cB
    riotass
    syld3an3
end
