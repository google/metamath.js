include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cima.mm"
include "cop.mm"
include "vex.mm"
include "elimasn.mm"
include "wb.mm"
include "opeliunxp.mm"
include "baib.mm"
include "adantl.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem iunsnima
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vy: setvar y
  assume iunsnima.1: |- ( ph -> A e. V )
  assume iunsnima.2: |- ( ( ph /\ x e. A ) -> B e. W )


  assert |- ( ( ph /\ x e. A ) -> ( U_ x e. A ( { x } X. B ) " { x } ) = B )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    vy
    vx
    cA
    @0
    csn
    #
    cB
    cxp
    ciun
    #
    @3
    cima
    #
    cB
    vy
    cv
    #
    @5
    wcel
    @0
    @6
    cop
    @4
    wcel
    #
    @2
    @6
    cB
    wcel
    #
    @4
    @0
    @6
    vx
    vex
    vy
    vex
    elimasn
    @1
    @7
    @8
    wb
    wph
    @7
    @1
    @8
    vx
    cA
    cB
    @6
    opeliunxp
    baib
    adantl
    syl5bb
    eqrdv
end
