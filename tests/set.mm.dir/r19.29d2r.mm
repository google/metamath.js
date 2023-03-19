include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "r19.29.mm"
include "syl2anc.mm"
include "reximi.mm"
include "syl.mm"

theorem r19.29d2r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r19.29d2r.1: |- ( ph -> A. x e. A A. y e. B ps )
  assume r19.29d2r.2: |- ( ph -> E. x e. A E. y e. B ch )


  assert |- ( ph -> E. x e. A E. y e. B ( ps /\ ch ) )

  proof
    wph
    wps
    vy
    cB
    wral
    #
    wch
    vy
    cB
    wrex
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
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wph
    @0
    vx
    cA
    wral
    @1
    vx
    cA
    wrex
    @3
    r19.29d2r.1
    r19.29d2r.2
    @0
    @1
    vx
    cA
    r19.29
    syl2anc
    @2
    @4
    vx
    cA
    wps
    wch
    vy
    cB
    r19.29
    reximi
    syl
end
