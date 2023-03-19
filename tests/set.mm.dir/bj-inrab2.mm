include "crab.mm"
include "cin.mm"
include "wa.mm"
include "bj-inrab.mm"
include "wceq.mm"
include "wtru.mm"
include "nfv.mm"
include "inidm.mm"
include "a1i.mm"
include "bj-rabeqd.mm"
include "trud.mm"
include "eqtri.mm"

theorem bj-inrab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } i^i { x e. A | ps } ) = { x e. A | ( ph /\ ps ) }

  proof
    wph
    vx
    cA
    crab
    wps
    vx
    cA
    crab
    cin
    wph
    wps
    wa
    #
    vx
    cA
    cA
    cin
    #
    crab
    #
    @0
    vx
    cA
    crab
    #
    wph
    wps
    vx
    cA
    cA
    bj-inrab
    @2
    @3
    wceq
    wtru
    @0
    vx
    @1
    cA
    wtru
    vx
    nfv
    @1
    cA
    wceq
    wtru
    cA
    inidm
    a1i
    bj-rabeqd
    trud
    eqtri
end
