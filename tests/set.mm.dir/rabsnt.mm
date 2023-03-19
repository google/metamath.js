include "crab.mm"
include "csn.mm"
include "wceq.mm"
include "wcel.mm"
include "snid.mm"
include "id.mm"
include "syl5eleqr.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"

theorem rabsnt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabsnt.1: |- B e. _V
  assume rabsnt.2: |- ( x = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( { x e. A | ph } = { B } -> ps )

  proof
    wph
    vx
    cA
    crab
    #
    cB
    csn
    #
    wceq
    #
    cB
    @0
    wcel
    #
    wps
    @2
    cB
    @1
    @0
    cB
    rabsnt.1
    snid
    @2
    id
    syl5eleqr
    @3
    cB
    cA
    wcel
    wps
    wph
    wps
    vx
    cB
    cA
    rabsnt.2
    elrab
    simprbi
    syl
end
