include "wsbc.mm"
include "cvv.mm"
include "wrex.mm"
include "wex.mm"
include "wcel.mm"
include "sbcex.mm"
include "rspesbca.mm"
include "mpancom.mm"
include "rexv.mm"
include "sylib.mm"

theorem spesbc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B


  assert |- ( [. A / x ]. ph -> E. x ph )

  proof
    wph
    vx
    cA
    wsbc
    #
    wph
    vx
    cvv
    wrex
    #
    wph
    vx
    wex
    cA
    cvv
    wcel
    @0
    @1
    wph
    vx
    cA
    sbcex
    wph
    vx
    cA
    cvv
    rspesbca
    mpancom
    wph
    vx
    rexv
    sylib
end
