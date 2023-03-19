include "con0.mm"
include "wcel.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "intminss.mm"
include "ex.mm"

theorem onintss
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume onintss.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( A e. On -> ( ps -> |^| { x e. On | ph } C_ A ) )

  proof
    cA
    con0
    wcel
    wps
    wph
    vx
    con0
    crab
    cint
    cA
    wss
    wph
    wps
    vx
    cA
    con0
    onintss.1
    intminss
    ex
end
