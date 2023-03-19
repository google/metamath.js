include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl23.mm"
include "jca.mm"
include "simpl33.mm"
include "simpl22.mm"
include "simpl3.mm"
include "simprl.mm"
include "paddasslem5.mm"
include "syl31anc.mm"
include "simprr.mm"
include "paddasslem6.mm"
include "syl32anc.mm"

theorem paddasslem7
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


  assert |- ( ( ( K e. HL /\ ( p e. A /\ r e. A /\ s e. A ) /\ ( x e. A /\ y e. A /\ z e. A ) ) /\ ( ( -. r .<_ ( x .\/ y ) /\ r .<_ ( y .\/ z ) /\ s .<_ ( x .\/ y ) ) /\ s .<_ ( p .\/ z ) ) ) -> p .<_ ( s .\/ z ) )

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
    vs
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
    w3a
    #
    @3
    @8
    @10
    c.or
    co
    #
    c.le
    wbr
    wn
    @3
    @10
    @12
    c.or
    co
    c.le
    wbr
    @5
    @16
    c.le
    wbr
    w3a
    #
    @5
    @1
    @12
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
    @2
    @6
    wa
    @13
    @5
    @12
    wne
    #
    @18
    @1
    @5
    @12
    c.or
    co
    c.le
    wbr
    @0
    @7
    @14
    @19
    simpl1
    #
    @20
    @2
    @6
    @2
    @4
    @6
    @0
    @14
    @19
    simpl21
    @2
    @4
    @6
    @0
    @14
    @19
    simpl23
    jca
    @9
    @11
    @13
    @0
    @7
    @19
    simpl33
    @20
    @0
    @4
    @14
    @17
    @21
    @22
    @2
    @4
    @6
    @0
    @14
    @19
    simpl22
    @0
    @7
    @14
    @19
    simpl3
    @15
    @17
    @18
    simprl
    vx
    vy
    vz
    cA
    c.or
    cK
    c.le
    vs
    vr
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem5
    syl31anc
    @15
    @17
    @18
    simprr
    vz
    cA
    c.or
    cK
    c.le
    vs
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem6
    syl32anc
end
