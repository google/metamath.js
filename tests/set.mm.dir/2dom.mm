include "c2o.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "wceq.mm"
include "wn.mm"
include "wrex.mm"
include "df2o2.mm"
include "breq1i.mm"
include "brdomi.mm"
include "sylbi.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "f1f.mm"
include "0ex.mm"
include "prid1.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "p0ex.mm"
include "prid2.mm"
include "0nep0.mm"
include "neii.mm"
include "wb.mm"
include "f1fveq.mm"
include "mpanr12.mm"
include "mtbiri.mm"
include "eqeq1.mm"
include "notbid.mm"
include "eqeq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "exlimiv.mm"
include "syl.mm"

theorem 2dom
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint A f
  assert |- ( 2o ~<_ A -> E. x e. A E. y e. A -. x = y )

  proof
    c2o
    cA
    cdom
    wbr
    #
    c0
    c0
    csn
    #
    cpr
    #
    cA
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    wn
    #
    vy
    cA
    wrex
    vx
    cA
    wrex
    #
    @0
    @2
    cA
    cdom
    wbr
    @5
    c2o
    @2
    cA
    cdom
    df2o2
    breq1i
    @2
    cA
    vf
    brdomi
    sylbi
    @4
    @10
    vf
    @4
    c0
    @3
    cfv
    #
    cA
    wcel
    #
    @1
    @3
    cfv
    #
    cA
    wcel
    #
    @11
    @13
    wceq
    #
    wn
    #
    @10
    @4
    @2
    cA
    @3
    wf
    #
    c0
    @2
    wcel
    #
    @12
    @2
    cA
    @3
    f1f
    #
    c0
    @1
    0ex
    prid1
    #
    @2
    cA
    c0
    @3
    ffvelrn
    sylancl
    @4
    @17
    @1
    @2
    wcel
    #
    @14
    @19
    c0
    @1
    p0ex
    prid2
    #
    @2
    cA
    @1
    @3
    ffvelrn
    sylancl
    @4
    @15
    c0
    @1
    wceq
    #
    c0
    @1
    0nep0
    neii
    @4
    @18
    @21
    @15
    @23
    wb
    @20
    @22
    @2
    cA
    c0
    @1
    @3
    f1fveq
    mpanr12
    mtbiri
    @9
    @16
    @11
    @7
    wceq
    #
    wn
    vx
    vy
    @11
    @13
    cA
    cA
    @6
    @11
    wceq
    @8
    @24
    @6
    @11
    @7
    eqeq1
    notbid
    @7
    @13
    wceq
    @24
    @15
    @7
    @13
    @11
    eqeq2
    notbid
    rspc2ev
    syl3anc
    exlimiv
    syl
end
