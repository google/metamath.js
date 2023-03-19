include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "simpl11.mm"
include "simpl21.mm"
include "simpl13.mm"
include "simpl22.mm"
include "3jca.mm"
include "simpl12.mm"
include "simpl23.mm"
include "jca.mm"
include "simpl32.mm"
include "simpl33.mm"
include "paddasslem1.mm"
include "syl31anc.mm"
include "simpl31.mm"
include "simprl.mm"
include "simpl2.mm"
include "simprr.mm"
include "paddasslem2.mm"
include "syl212anc.mm"
include "jca31.mm"
include "paddasslem3.mm"
include "sylc.mm"

theorem paddasslem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )

  disjoint A s
  disjoint .\/ s
  disjoint K s
  disjoint .<_ s
  disjoint p s
  disjoint r s
  disjoint s x
  disjoint s y
  disjoint s z
  assert |- ( ( ( ( K e. HL /\ p e. A /\ r e. A ) /\ ( x e. A /\ y e. A /\ z e. A ) /\ ( p =/= z /\ x =/= y /\ -. r .<_ ( x .\/ y ) ) ) /\ ( p .<_ ( x .\/ r ) /\ r .<_ ( y .\/ z ) ) ) -> E. s e. A ( s .<_ ( x .\/ y ) /\ s .<_ ( p .\/ z ) ) )

  proof
    cK
    chlt
    wcel
    #
    vp
    cv
    #
    cA
    wcel
    #
    vr
    cv
    #
    cA
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    w3a
    #
    @1
    @10
    wne
    #
    @6
    @8
    wne
    #
    @3
    @6
    @8
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    @1
    @6
    @3
    c.or
    co
    c.le
    wbr
    #
    @3
    @8
    @10
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @0
    @7
    @4
    @9
    w3a
    #
    @2
    @11
    wa
    #
    w3a
    @6
    @3
    @8
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @13
    wa
    @19
    @10
    @25
    c.le
    wbr
    #
    wa
    #
    wa
    vs
    cv
    #
    @15
    c.le
    wbr
    @29
    @1
    @10
    c.or
    co
    c.le
    wbr
    wa
    vs
    cA
    wrex
    @22
    @0
    @23
    @24
    @0
    @2
    @4
    @12
    @17
    @21
    simpl11
    #
    @22
    @7
    @4
    @9
    @7
    @9
    @11
    @5
    @17
    @21
    simpl21
    @0
    @2
    @4
    @12
    @17
    @21
    simpl13
    #
    @7
    @9
    @11
    @5
    @17
    @21
    simpl22
    3jca
    #
    @22
    @2
    @11
    @0
    @2
    @4
    @12
    @17
    @21
    simpl12
    @7
    @9
    @11
    @5
    @17
    @21
    simpl23
    jca
    3jca
    @22
    @26
    @13
    @28
    @22
    @0
    @23
    @14
    @16
    @26
    @30
    @32
    @13
    @14
    @16
    @5
    @12
    @21
    simpl32
    @13
    @14
    @16
    @5
    @12
    @21
    simpl33
    #
    vx
    vy
    cA
    c.or
    cK
    c.le
    vr
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem1
    syl31anc
    @13
    @14
    @16
    @5
    @12
    @21
    simpl31
    @22
    @19
    @27
    @18
    @19
    @20
    simprl
    @22
    @0
    @4
    @12
    @16
    @20
    @27
    @30
    @31
    @5
    @12
    @17
    @21
    simpl2
    @33
    @18
    @19
    @20
    simprr
    vx
    vy
    vz
    cA
    c.or
    cK
    c.le
    vr
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem2
    syl212anc
    jca
    jca31
    vx
    vy
    vz
    cA
    c.or
    cK
    c.le
    vs
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem3
    sylc
end
