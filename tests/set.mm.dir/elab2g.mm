include "wcel.mm"
include "cab.mm"
include "eleq2i.mm"
include "elabg.mm"
include "syl5bb.mm"

theorem elab2g
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume elab2g.1: |- ( x = A -> ( ph <-> ps ) )
  assume elab2g.2: |- B = { x | ph }

  disjoint ps x
  disjoint A x
  assert |- ( A e. V -> ( A e. B <-> ps ) )

  proof
    cA
    cB
    wcel
    cA
    wph
    vx
    cab
    #
    wcel
    cA
    cV
    wcel
    wps
    cB
    @0
    cA
    elab2g.2
    eleq2i
    wph
    wps
    vx
    cA
    cV
    elab2g.1
    elabg
    syl5bb
end
