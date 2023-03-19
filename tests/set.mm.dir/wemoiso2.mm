include "wwe.mm"
include "cv.mm"
include "wiso.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wse.mm"
include "simpl.mm"
include "cvv.mm"
include "wcel.mm"
include "crn.mm"
include "wf1o.mm"
include "wfo.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "ad2antrl.mm"
include "exse.mm"
include "syl.mm"
include "jca.mm"
include "weisoeq2.mm"
include "sylancom.mm"
include "ex.mm"
include "alrimivv.mm"
include "isoeq1.mm"
include "mo4.mm"
include "sylibr.mm"

theorem wemoiso2
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g

  disjoint R f
  disjoint A f
  disjoint S f
  disjoint B f
  disjoint R g
  disjoint f g
  disjoint A g
  disjoint S g
  disjoint B g
  assert |- ( S We B -> E* f f Isom R , S ( A , B ) )

  proof
    cB
    cS
    wwe
    #
    cA
    cB
    cR
    cS
    vf
    cv
    #
    wiso
    #
    cA
    cB
    cR
    cS
    vg
    cv
    #
    wiso
    #
    wa
    #
    @1
    @3
    wceq
    #
    wi
    #
    vg
    wal
    vf
    wal
    @2
    vf
    wmo
    @0
    @7
    vf
    vg
    @0
    @5
    @6
    @0
    @5
    @0
    cB
    cS
    wse
    #
    wa
    @6
    @0
    @5
    wa
    #
    @0
    @8
    @0
    @5
    simpl
    @9
    cB
    cvv
    wcel
    #
    @8
    @2
    @10
    @0
    @4
    @2
    cB
    @1
    crn
    #
    cvv
    @2
    cA
    cB
    @1
    wf1o
    cA
    cB
    @1
    wfo
    @11
    cB
    wceq
    cA
    cB
    cR
    cS
    @1
    isof1o
    cA
    cB
    @1
    f1ofo
    cA
    cB
    @1
    forn
    3syl
    @1
    vf
    vex
    rnex
    syl6eqelr
    ad2antrl
    cB
    cS
    cvv
    exse
    syl
    jca
    cA
    cB
    cR
    cS
    @1
    @3
    weisoeq2
    sylancom
    ex
    alrimivv
    @2
    @4
    vf
    vg
    cA
    cB
    cR
    cS
    @3
    @1
    isoeq1
    mo4
    sylibr
end
