include "wer.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "cec.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "wi.mm"
include "simpr.mm"
include "simpl.mm"
include "erref.mm"
include "weq.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "expr.mm"
include "syl2anc.mm"
include "simplll.mm"
include "simprl.mm"
include "simprr.mm"
include "ertr3d.mm"
include "ex.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "vex.mm"
include "elec.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "syl6bbr.mm"

theorem prtlem10
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let c.sm: class .~

  disjoint v w
  disjoint v z
  disjoint A v
  disjoint .~ v
  assert |- ( .~ Er A -> ( z e. A -> ( z .~ w <-> E. v e. A ( z e. [ v ] .~ /\ w e. [ v ] .~ ) ) ) )

  proof
    cA
    c.sm
    wer
    #
    vz
    cv
    #
    cA
    wcel
    #
    @1
    vw
    cv
    #
    c.sm
    wbr
    #
    @1
    vv
    cv
    #
    c.sm
    cec
    #
    wcel
    #
    @3
    @6
    wcel
    #
    wa
    #
    vv
    cA
    wrex
    #
    wb
    @0
    @2
    wa
    #
    @4
    @5
    @1
    c.sm
    wbr
    #
    @5
    @3
    c.sm
    wbr
    #
    wa
    #
    vv
    cA
    wrex
    #
    @10
    @11
    @4
    @15
    @11
    @2
    @1
    @1
    c.sm
    wbr
    #
    @4
    @15
    wi
    @0
    @2
    simpr
    #
    @11
    @1
    c.sm
    cA
    @0
    @2
    simpl
    @17
    erref
    @2
    @16
    @4
    @15
    @14
    @16
    @4
    wa
    vv
    @1
    cA
    vv
    vz
    weq
    @12
    @16
    @13
    @4
    @5
    @1
    @1
    c.sm
    breq1
    @5
    @1
    @3
    c.sm
    breq1
    anbi12d
    rspcev
    expr
    syl2anc
    @11
    @14
    @4
    vv
    cA
    @11
    @5
    cA
    wcel
    #
    wa
    #
    @14
    @4
    @19
    @14
    wa
    @1
    @5
    @3
    c.sm
    cA
    @0
    @2
    @18
    @14
    simplll
    @19
    @12
    @13
    simprl
    @19
    @12
    @13
    simprr
    ertr3d
    ex
    rexlimdva
    impbid
    @9
    @14
    vv
    cA
    @7
    @12
    @8
    @13
    @1
    @5
    c.sm
    vz
    vex
    vv
    vex
    #
    elec
    @3
    @5
    c.sm
    vw
    vex
    @20
    elec
    anbi12i
    rexbii
    syl6bbr
    ex
end
