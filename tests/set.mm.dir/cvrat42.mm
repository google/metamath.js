include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cvrat4.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simplr3.mm"
include "atbase.mm"
include "syl.mm"
include "adantl.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "sylibd.mm"

theorem cvrat42
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  assume cvrat4.b: |- B = ( Base ` K )
  assume cvrat4.l: |- .<_ = ( le ` K )
  assume cvrat4.j: |- .\/ = ( join ` K )
  assume cvrat4.z: |- .0. = ( 0. ` K )
  assume cvrat4.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint B r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint X r
  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) ) -> ( ( X =/= .0. /\ P .<_ ( X .\/ Q ) ) -> E. r e. A ( r .<_ X /\ P .<_ ( r .\/ Q ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    wa
    #
    cX
    c.0
    wne
    cP
    cX
    cQ
    c.or
    co
    c.le
    wbr
    wa
    vr
    cv
    #
    cX
    c.le
    wbr
    #
    cP
    cQ
    @6
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vr
    cA
    wrex
    @7
    cP
    @6
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vr
    cA
    wrex
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    cX
    c.0
    vr
    cvrat4.b
    cvrat4.l
    cvrat4.j
    cvrat4.z
    cvrat4.a
    cvrat4
    @5
    @10
    @13
    vr
    cA
    @5
    @6
    cA
    wcel
    #
    wa
    #
    @9
    @12
    @7
    @15
    @8
    @11
    cP
    c.le
    @15
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @8
    @11
    wceq
    @0
    @16
    @4
    @14
    cK
    hllat
    ad2antrr
    @15
    @3
    @17
    @1
    @2
    @3
    @0
    @14
    simplr3
    cA
    cB
    cQ
    cK
    cvrat4.b
    cvrat4.a
    atbase
    syl
    @14
    @18
    @5
    cA
    cB
    @6
    cK
    cvrat4.b
    cvrat4.a
    atbase
    adantl
    cB
    c.or
    cK
    cQ
    @6
    cvrat4.b
    cvrat4.j
    latjcom
    syl3anc
    breq2d
    anbi2d
    rexbidva
    sylibd
end
