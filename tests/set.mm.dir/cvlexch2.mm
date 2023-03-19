include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cvlexch1.mm"
include "clat.mm"
include "wceq.mm"
include "cvllat.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "atbase.mm"
include "syl.mm"
include "simp23.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "simp21.mm"
include "3imtr4d.mm"

theorem cvlexch2
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  assume cvlexch.b: |- B = ( Base ` K )
  assume cvlexch.l: |- .<_ = ( le ` K )
  assume cvlexch.j: |- .\/ = ( join ` K )
  assume cvlexch.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ X e. B ) /\ -. P .<_ X ) -> ( P .<_ ( Q .\/ X ) -> Q .<_ ( P .\/ X ) ) )

  proof
    cK
    clc
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
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    wn
    #
    w3a
    #
    cP
    cX
    cQ
    c.or
    co
    #
    c.le
    wbr
    cQ
    cX
    cP
    c.or
    co
    #
    c.le
    wbr
    cP
    cQ
    cX
    c.or
    co
    #
    c.le
    wbr
    cQ
    cP
    cX
    c.or
    co
    #
    c.le
    wbr
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    cX
    cvlexch.b
    cvlexch.l
    cvlexch.j
    cvlexch.a
    cvlexch1
    @6
    @9
    @7
    cP
    c.le
    @6
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @3
    @9
    @7
    wceq
    @0
    @4
    @11
    @5
    cK
    cvllat
    3ad2ant1
    #
    @6
    @2
    @12
    @0
    @1
    @2
    @3
    @5
    simp22
    cA
    cB
    cQ
    cK
    cvlexch.b
    cvlexch.a
    atbase
    syl
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    cB
    c.or
    cK
    cQ
    cX
    cvlexch.b
    cvlexch.j
    latjcom
    syl3anc
    breq2d
    @6
    @10
    @8
    cQ
    c.le
    @6
    @11
    cP
    cB
    wcel
    #
    @3
    @10
    @8
    wceq
    @13
    @6
    @1
    @15
    @0
    @1
    @2
    @3
    @5
    simp21
    cA
    cB
    cP
    cK
    cvlexch.b
    cvlexch.a
    atbase
    syl
    @14
    cB
    c.or
    cK
    cP
    cX
    cvlexch.b
    cvlexch.j
    latjcom
    syl3anc
    breq2d
    3imtr4d
end
