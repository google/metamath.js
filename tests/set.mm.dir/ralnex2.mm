include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "notnotb.mm"
include "2rexbii.mm"
include "rexnal2.mm"
include "bitr2i.mm"
include "xchbinx.mm"

theorem ralnex2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( A. x e. A A. y e. B -. ph <-> -. E. x e. A E. y e. B ph )

  proof
    wph
    wn
    #
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
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @1
    notnotb
    @3
    @0
    wn
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @2
    wph
    @4
    vx
    vy
    cA
    cB
    wph
    notnotb
    2rexbii
    @0
    vx
    vy
    cA
    cB
    rexnal2
    bitr2i
    xchbinx
end
