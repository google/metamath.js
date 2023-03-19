include "wcel.mm"
include "cab.mm"
include "cint.mm"
include "wss.mm"
include "elabg.mm"
include "mpbiri.mm"
include "intss1.mm"
include "syl.mm"

theorem intmin3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume intmin3.2: |- ( x = A -> ( ph <-> ps ) )
  assume intmin3.3: |- ps

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> |^| { x | ph } C_ A )

  proof
    cA
    cV
    wcel
    #
    cA
    wph
    vx
    cab
    #
    wcel
    #
    @1
    cint
    cA
    wss
    @0
    @2
    wps
    intmin3.3
    wph
    wps
    vx
    cA
    cV
    intmin3.2
    elabg
    mpbiri
    cA
    @1
    intss1
    syl
end
