include "wcel.mm"
include "cab.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "weu.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "imp.mm"
include "euabsn2.mm"
include "sylibr.mm"

theorem absneu
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( ( A e. V /\ { x | ph } = { A } ) -> E! x ph )

  proof
    cA
    cV
    wcel
    #
    wph
    vx
    cab
    #
    cA
    csn
    #
    wceq
    #
    wa
    @1
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    wex
    #
    wph
    vx
    weu
    @0
    @3
    @7
    @6
    @3
    vy
    cA
    cV
    @4
    cA
    wceq
    @5
    @2
    @1
    @4
    cA
    sneq
    eqeq2d
    spcegv
    imp
    wph
    vx
    vy
    euabsn2
    sylibr
end
