include "cv.mm"
include "cif.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ifeq1.mm"
include "eleq1d.mm"
include "ifeq2.mm"
include "vex.mm"
include "ifex.mm"
include "vtocl2g.mm"

theorem ifexg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> if ( ph , A , B ) e. _V )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cif
    #
    cvv
    wcel
    wph
    cA
    @1
    cif
    #
    cvv
    wcel
    wph
    cA
    cB
    cif
    #
    cvv
    wcel
    vx
    vy
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    @2
    @3
    cvv
    wph
    @0
    cA
    @1
    ifeq1
    eleq1d
    @1
    cB
    wceq
    @3
    @4
    cvv
    wph
    @1
    cB
    cA
    ifeq2
    eleq1d
    wph
    @0
    @1
    vx
    vex
    vy
    vex
    ifex
    vtocl2g
end
