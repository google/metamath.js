include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "lhpexle1.mm"
include "wbr.mm"
include "w3a.mm"
include "wrex.mm"
include "adantr.mm"
include "lhpexle2lem.mm"
include "3expa.mm"
include "lhpexle1lem.mm"
include "3ancomb.mm"
include "rexbii.mm"
include "sylib.mm"

theorem lhpexle2
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let cZ: class Z
  assume lhpex1.l: |- .<_ = ( le ` K )
  assume lhpex1.a: |- A = ( Atoms ` K )
  assume lhpex1.h: |- H = ( LHyp ` K )

  disjoint .<_ p
  disjoint A p
  disjoint H p
  disjoint K p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A ( p .<_ W /\ p =/= X /\ p =/= Y ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vp
    cv
    #
    cX
    wne
    #
    cA
    c.le
    cW
    cY
    vp
    cA
    cH
    cK
    c.le
    cW
    cX
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle1
    @0
    cY
    cA
    wcel
    cY
    cW
    c.le
    wbr
    wa
    #
    wa
    #
    @1
    cW
    c.le
    wbr
    #
    @1
    cY
    wne
    #
    @2
    w3a
    #
    vp
    cA
    wrex
    #
    @5
    @2
    @6
    w3a
    #
    vp
    cA
    wrex
    @4
    @6
    cA
    c.le
    cW
    cX
    vp
    @0
    @5
    @6
    wa
    vp
    cA
    wrex
    @3
    cA
    cH
    cK
    c.le
    cW
    cY
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle1
    adantr
    @0
    @3
    cX
    cA
    wcel
    cX
    cW
    c.le
    wbr
    wa
    @8
    cA
    cH
    cK
    c.le
    cW
    cY
    cX
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle2lem
    3expa
    lhpexle1lem
    @7
    @9
    vp
    cA
    @5
    @6
    @2
    3ancomb
    rexbii
    sylib
    lhpexle1lem
end
