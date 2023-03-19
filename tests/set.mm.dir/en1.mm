include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "c0.mm"
include "wf1o.mm"
include "df1o2.mm"
include "breq2i.mm"
include "bren.mm"
include "bitri.mm"
include "ccnv.mm"
include "cfv.mm"
include "f1ocnv.mm"
include "crn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "cop.mm"
include "wf.mm"
include "f1of.mm"
include "wcel.mm"
include "0ex.mm"
include "fsn2.mm"
include "simprbi.mm"
include "rneqd.mm"
include "rnsnop.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "fvex.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "spcev.mm"
include "3syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "vex.mm"
include "ensn1.mm"
include "breq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem en1
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let wph: wff ph

  disjoint A x
  disjoint f x
  disjoint x y
  disjoint f y
  disjoint A f
  disjoint A y
  disjoint ph y
  assert |- ( A ~~ 1o <-> E. x A = { x } )

  proof
    cA
    c1o
    cen
    wbr
    #
    cA
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    #
    @0
    cA
    c0
    csn
    #
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @4
    @0
    cA
    @5
    cen
    wbr
    @8
    c1o
    @5
    cA
    cen
    df1o2
    breq2i
    cA
    @5
    vf
    bren
    bitri
    @7
    @4
    vf
    @7
    @5
    cA
    @6
    ccnv
    #
    wf1o
    #
    cA
    c0
    @9
    cfv
    #
    csn
    #
    wceq
    #
    @4
    cA
    @5
    @6
    f1ocnv
    @10
    @9
    crn
    #
    cA
    @12
    @10
    @5
    cA
    @9
    wfo
    @14
    cA
    wceq
    @5
    cA
    @9
    f1ofo
    @5
    cA
    @9
    forn
    syl
    @10
    @14
    c0
    @11
    cop
    csn
    #
    crn
    @12
    @10
    @9
    @15
    @10
    @5
    cA
    @9
    wf
    #
    @9
    @15
    wceq
    #
    @5
    cA
    @9
    f1of
    @16
    @11
    cA
    wcel
    @17
    c0
    cA
    @9
    0ex
    fsn2
    simprbi
    syl
    rneqd
    c0
    @11
    0ex
    rnsnop
    syl6eq
    eqtr3d
    @3
    @13
    vx
    @11
    c0
    @9
    fvex
    @1
    @11
    wceq
    @2
    @12
    cA
    @1
    @11
    sneq
    eqeq2d
    spcev
    3syl
    exlimiv
    sylbi
    @3
    @0
    vx
    @3
    @0
    @2
    c1o
    cen
    wbr
    @1
    vx
    vex
    ensn1
    cA
    @2
    c1o
    cen
    breq1
    mpbiri
    exlimiv
    impbii
end
