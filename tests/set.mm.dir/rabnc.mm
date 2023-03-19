include "crab.mm"
include "wn.mm"
include "cin.mm"
include "wa.mm"
include "c0.mm"
include "inrab.mm"
include "wceq.mm"
include "wral.mm"
include "pm3.24.mm"
include "rgenw.mm"
include "rabeq0.mm"
include "mpbir.mm"
include "eqtri.mm"

theorem rabnc
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( { x e. A | ph } i^i { x e. A | -. ph } ) = (/)

  proof
    wph
    vx
    cA
    crab
    wph
    wn
    #
    vx
    cA
    crab
    cin
    wph
    @0
    wa
    #
    vx
    cA
    crab
    #
    c0
    wph
    @0
    vx
    cA
    inrab
    @2
    c0
    wceq
    @1
    wn
    #
    vx
    cA
    wral
    @3
    vx
    cA
    wph
    pm3.24
    rgenw
    @1
    vx
    cA
    rabeq0
    mpbir
    eqtri
end
