include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "notnotb.mm"
include "rexbii.mm"
include "2rexbii.mm"
include "rexnal3.mm"
include "bitr2i.mm"
include "xchbinx.mm"

theorem ralnex3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A. x e. A A. y e. B A. z e. C -. ph <-> -. E. x e. A E. y e. B E. z e. C ph )

  proof
    wph
    wn
    #
    vz
    cC
    wral
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @1
    wn
    #
    wph
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
    #
    @1
    notnotb
    @4
    @0
    wn
    #
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
    @2
    @3
    @6
    vx
    vy
    cA
    cB
    wph
    @5
    vz
    cC
    wph
    notnotb
    rexbii
    2rexbii
    @0
    vx
    vy
    vz
    cA
    cB
    cC
    rexnal3
    bitr2i
    xchbinx
end
