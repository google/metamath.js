include "wn.mm"
include "wrex.mm"
include "wral.mm"
include "rexnal.mm"
include "rexbii.mm"
include "bitri.mm"

theorem rexnal2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( E. x e. A E. y e. B -. ph <-> -. A. x e. A A. y e. B ph )

  proof
    wph
    wn
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wph
    vy
    cB
    wral
    #
    wn
    #
    vx
    cA
    wrex
    @1
    vx
    cA
    wral
    wn
    @0
    @2
    vx
    cA
    wph
    vy
    cB
    rexnal
    rexbii
    @1
    vx
    cA
    rexnal
    bitri
end
