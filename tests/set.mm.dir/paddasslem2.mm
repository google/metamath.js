include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp23.mm"
include "simp22.mm"
include "3jca.mm"
include "simp21.mm"
include "simp3l.mm"
include "atnlej2.mm"
include "syl131anc.mm"
include "simp3r.mm"
include "hlatexch1.mm"
include "sylc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breqtrrd.mm"

theorem paddasslem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vr: setvar r
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ r e. A ) /\ ( x e. A /\ y e. A /\ z e. A ) /\ ( -. r .<_ ( x .\/ y ) /\ r .<_ ( y .\/ z ) ) ) -> z .<_ ( r .\/ y ) )

  proof
    cK
    chlt
    wcel
    #
    vr
    cv
    #
    cA
    wcel
    #
    wa
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
    @4
    @6
    c.or
    co
    c.le
    wbr
    wn
    #
    @1
    @6
    @8
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @8
    @6
    @1
    c.or
    co
    #
    @1
    @6
    c.or
    co
    #
    c.le
    @14
    @0
    @2
    @9
    @7
    w3a
    #
    @1
    @6
    wne
    #
    w3a
    @12
    @8
    @15
    c.le
    wbr
    @14
    @0
    @17
    @18
    @0
    @2
    @10
    @13
    simp1l
    #
    @14
    @2
    @9
    @7
    @0
    @2
    @10
    @13
    simp1r
    #
    @3
    @5
    @7
    @9
    @13
    simp23
    @3
    @5
    @7
    @9
    @13
    simp22
    #
    3jca
    @14
    @0
    @2
    @5
    @7
    @11
    @18
    @19
    @20
    @3
    @5
    @7
    @9
    @13
    simp21
    @21
    @3
    @10
    @11
    @12
    simp3l
    cA
    @1
    @4
    @6
    c.or
    cK
    c.le
    paddasslem.l
    paddasslem.j
    paddasslem.a
    atnlej2
    syl131anc
    3jca
    @3
    @10
    @11
    @12
    simp3r
    cA
    @1
    @8
    @6
    c.or
    cK
    c.le
    paddasslem.l
    paddasslem.j
    paddasslem.a
    hlatexch1
    sylc
    @14
    cK
    clat
    wcel
    #
    @1
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @23
    wcel
    #
    @16
    @15
    wceq
    @14
    @0
    @22
    @19
    cK
    hllat
    syl
    @14
    @2
    @24
    @20
    cA
    @23
    @1
    cK
    @23
    eqid
    #
    paddasslem.a
    atbase
    syl
    @14
    @7
    @25
    @21
    cA
    @23
    @6
    cK
    @26
    paddasslem.a
    atbase
    syl
    @23
    c.or
    cK
    @1
    @6
    @26
    paddasslem.j
    latjcom
    syl3anc
    breqtrrd
end
