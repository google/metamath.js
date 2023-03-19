include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "encv.mm"
include "wfn.mm"
include "f1ofn.mm"
include "cdm.mm"
include "fndm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "syl.mm"
include "crn.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "rnex.mm"
include "jca.mm"
include "exlimiv.mm"
include "f1oeq2.mm"
include "exbidv.mm"
include "f1oeq3.mm"
include "df-en.mm"
include "brabg.mm"
include "pm5.21nii.mm"

theorem bren
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cC: class C

  disjoint A f
  disjoint B f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  assert |- ( A ~~ B <-> E. f f : A -1-1-onto-> B )

  proof
    cA
    cB
    cen
    wbr
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
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
    cA
    cB
    encv
    @4
    @2
    vf
    @4
    @0
    @1
    @4
    @3
    cA
    wfn
    #
    @0
    cA
    cB
    @3
    f1ofn
    @6
    cA
    @3
    cdm
    cvv
    cA
    @3
    fndm
    @3
    vf
    vex
    #
    dmex
    syl6eqelr
    syl
    @4
    cB
    @3
    crn
    #
    cvv
    @4
    cA
    cB
    @3
    wfo
    @8
    cB
    wceq
    cA
    cB
    @3
    f1ofo
    cA
    cB
    @3
    forn
    syl
    @3
    @7
    rnex
    syl6eqelr
    jca
    exlimiv
    vx
    cv
    #
    vy
    cv
    #
    @3
    wf1o
    #
    vf
    wex
    cA
    @10
    @3
    wf1o
    #
    vf
    wex
    @5
    vx
    vy
    cA
    cB
    cvv
    cvv
    cen
    @9
    cA
    wceq
    @11
    @12
    vf
    @9
    cA
    @10
    @3
    f1oeq2
    exbidv
    @10
    cB
    wceq
    @12
    @4
    vf
    @10
    cB
    cA
    @3
    f1oeq3
    exbidv
    vx
    vy
    vf
    df-en
    brabg
    pm5.21nii
end
