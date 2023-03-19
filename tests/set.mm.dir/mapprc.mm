include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "abn0.mm"
include "cdm.mm"
include "fdm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "necon1bi.mm"

theorem mapprc
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint A f
  disjoint B f
  assert |- ( -. A e. _V -> { f | f : A --> B } = (/) )

  proof
    cA
    cvv
    wcel
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    vf
    cab
    #
    c0
    @3
    c0
    wne
    @2
    vf
    wex
    @0
    @2
    vf
    abn0
    @2
    @0
    vf
    @2
    cA
    @1
    cdm
    cvv
    cA
    cB
    @1
    fdm
    @1
    vf
    vex
    dmex
    syl6eqelr
    exlimiv
    sylbi
    necon1bi
end
