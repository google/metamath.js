include "wn.mm"
include "wrex.mm"
include "wral.mm"
include "rexnal.mm"
include "2rexbii.mm"
include "rexnal2.mm"
include "bitri.mm"

theorem rexnal3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( E. x e. A E. y e. B E. z e. C -. ph <-> -. A. x e. A A. y e. B A. z e. C ph )

  proof
    wph
    wn
    vz
    cC
    wrex
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    wph
    vz
    cC
    wral
    #
    wn
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @1
    vy
    cB
    wral
    vx
    cA
    wral
    wn
    @0
    @2
    vx
    vy
    cA
    cB
    wph
    vz
    cC
    rexnal
    2rexbii
    @1
    vx
    vy
    cA
    cB
    rexnal2
    bitri
end
