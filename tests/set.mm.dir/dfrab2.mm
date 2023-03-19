include "crab.mm"
include "cab.mm"
include "cin.mm"
include "dfrab3.mm"
include "incom.mm"
include "eqtri.mm"

theorem dfrab2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- { x e. A | ph } = ( { x | ph } i^i A )

  proof
    wph
    vx
    cA
    crab
    cA
    wph
    vx
    cab
    #
    cin
    @0
    cA
    cin
    wph
    vx
    cA
    dfrab3
    cA
    @0
    incom
    eqtri
end
