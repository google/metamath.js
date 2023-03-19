include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "simpl2l.mm"
include "simpl3.mm"
include "3jca.mm"
include "simprl.mm"
include "simprr.mm"
include "hlatexch2.mm"
include "sylc.mm"

theorem paddasslem6
  let vz: setvar z
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vp: setvar p
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( p e. A /\ s e. A ) /\ z e. A ) /\ ( s =/= z /\ s .<_ ( p .\/ z ) ) ) -> p .<_ ( s .\/ z ) )

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
    vs
    cv
    #
    cA
    wcel
    #
    wa
    #
    vz
    cv
    #
    cA
    wcel
    #
    w3a
    #
    @3
    @6
    wne
    #
    @3
    @1
    @6
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
    @4
    @2
    @7
    w3a
    #
    @9
    w3a
    @10
    @1
    @3
    @6
    c.or
    co
    c.le
    wbr
    @12
    @0
    @13
    @9
    @0
    @5
    @7
    @11
    simpl1
    @12
    @4
    @2
    @7
    @2
    @4
    @0
    @7
    @11
    simpl2r
    @2
    @4
    @0
    @7
    @11
    simpl2l
    @0
    @5
    @7
    @11
    simpl3
    3jca
    @8
    @9
    @10
    simprl
    3jca
    @8
    @9
    @10
    simprr
    cA
    @3
    @1
    @6
    c.or
    cK
    c.le
    paddasslem.l
    paddasslem.j
    paddasslem.a
    hlatexch2
    sylc
end
