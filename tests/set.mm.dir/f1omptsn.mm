include "wf1o.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "sneq.mm"
include "cbvmptv.mm"
include "eqcomi.mm"
include "id.mm"
include "eqeqan12d.mm"
include "cbvrexdva.mm"
include "cbvabv.mm"
include "f1omptsnlem.mm"
include "wb.mm"
include "eqtri.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "f1oeq1.mm"

theorem f1omptsn
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cF: class F
  let va: setvar a
  let vz: setvar z
  assume f1omptsn.f: |- F = ( x e. A |-> { x } )
  assume f1omptsn.r: |- R = { u | E. x e. A u = { x } }

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint A a
  disjoint A z
  disjoint a u
  disjoint a x
  disjoint a z
  disjoint u z
  disjoint x z
  assert |- F : A -1-1-onto-> R

  proof
    cA
    cR
    cF
    wf1o
    #
    cA
    cR
    va
    cA
    va
    cv
    #
    csn
    #
    cmpt
    #
    wf1o
    #
    @4
    cA
    vz
    cv
    #
    @2
    wceq
    #
    va
    cA
    wrex
    #
    vz
    cab
    #
    @3
    wf1o
    #
    vx
    vu
    cA
    @8
    @3
    vx
    cA
    vx
    cv
    #
    csn
    #
    cmpt
    #
    @3
    vx
    va
    cA
    @11
    @2
    @10
    @1
    sneq
    #
    cbvmptv
    #
    eqcomi
    vu
    cv
    #
    @11
    wceq
    #
    vx
    cA
    wrex
    #
    vu
    cab
    #
    @8
    @17
    @7
    vu
    vz
    @15
    @5
    wceq
    #
    @16
    @6
    vx
    va
    cA
    @19
    @10
    @1
    wceq
    @15
    @5
    @11
    @2
    @19
    id
    @13
    eqeqan12d
    cbvrexdva
    cbvabv
    #
    eqcomi
    f1omptsnlem
    cR
    @8
    wceq
    @4
    @9
    wb
    cR
    @18
    @8
    f1omptsn.r
    @20
    eqtri
    cR
    @8
    cA
    @3
    f1oeq3
    ax-mp
    mpbir
    cF
    @3
    wceq
    @0
    @4
    wb
    cF
    @12
    @3
    f1omptsn.f
    @14
    eqtri
    cA
    cR
    cF
    @3
    f1oeq1
    ax-mp
    mpbir
end
