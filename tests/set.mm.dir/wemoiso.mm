include "wwe.mm"
include "cv.mm"
include "wiso.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wse.mm"
include "simpl.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "vex.mm"
include "wf1o.mm"
include "isof1o.mm"
include "f1of.mm"
include "syl.mm"
include "dmfex.mm"
include "sylancr.mm"
include "ad2antrl.mm"
include "exse.mm"
include "jca.mm"
include "weisoeq.mm"
include "sylancom.mm"
include "ex.mm"
include "alrimivv.mm"
include "isoeq1.mm"
include "mo4.mm"
include "sylibr.mm"

theorem wemoiso
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
  assert |- ( R We A -> E* f f Isom R , S ( A , B ) )

  proof
    cA
    cR
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
    vf
    vg
    weq
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
    cA
    cR
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
    cA
    cvv
    wcel
    #
    @8
    @2
    @10
    @0
    @4
    @2
    @1
    cvv
    wcel
    cA
    cB
    @1
    wf
    #
    @10
    vf
    vex
    @2
    cA
    cB
    @1
    wf1o
    @11
    cA
    cB
    cR
    cS
    @1
    isof1o
    cA
    cB
    @1
    f1of
    syl
    cA
    cB
    cvv
    @1
    dmfex
    sylancr
    ad2antrl
    cA
    cR
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
    weisoeq
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
