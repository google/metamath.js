include "cfzo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "elfzolt3b.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "ne0i.mm"
include "impbii.mm"

theorem fzon0
  let cM: class M
  let cN: class N
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- ( ( M ..^ N ) =/= (/) <-> M e. ( M ..^ N ) )

  proof
    cM
    cN
    cfzo
    co
    #
    c0
    wne
    #
    cM
    @0
    wcel
    #
    @1
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @2
    vx
    @0
    n0
    @4
    @2
    vx
    @3
    cM
    cN
    elfzolt3b
    exlimiv
    sylbi
    @0
    cM
    ne0i
    impbii
end
