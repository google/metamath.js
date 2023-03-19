include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "ccnv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "cnvex.mm"
include "f1ocnv.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem f1oexbi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g

  disjoint A f
  disjoint A g
  disjoint f g
  disjoint B f
  disjoint B g
  assert |- ( E. f f : A -1-1-onto-> B <-> E. g g : B -1-1-onto-> A )

  proof
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cB
    cA
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    @1
    @5
    vf
    @0
    ccnv
    #
    cvv
    wcel
    @1
    cB
    cA
    @6
    wf1o
    #
    @5
    @0
    vf
    vex
    cnvex
    cA
    cB
    @0
    f1ocnv
    @4
    @7
    vg
    @6
    cvv
    cB
    cA
    @3
    @6
    f1oeq1
    spcegv
    mpsyl
    exlimiv
    @4
    @2
    vg
    @3
    ccnv
    #
    cvv
    wcel
    @4
    cA
    cB
    @8
    wf1o
    #
    @2
    @3
    vg
    vex
    cnvex
    cB
    cA
    @3
    f1ocnv
    @1
    @9
    vf
    @8
    cvv
    cA
    cB
    @0
    @8
    f1oeq1
    spcegv
    mpsyl
    exlimiv
    impbii
end
