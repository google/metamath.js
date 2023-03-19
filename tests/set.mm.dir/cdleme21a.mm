include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "clc.mm"
include "wne.mm"
include "simp11.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp12.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simp13.mm"
include "simp2r.mm"
include "atnlej1.mm"
include "necomd.mm"
include "syl131anc.mm"
include "simp3r.mm"
include "cvlsupr6.mm"
include "syl132anc.mm"

theorem cdleme21a
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume cdleme21a.l: |- .<_ = ( le ` K )
  assume cdleme21a.j: |- .\/ = ( join ` K )
  assume cdleme21a.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( S e. A /\ -. S .<_ ( P .\/ Q ) ) /\ ( z e. A /\ ( P .\/ z ) = ( S .\/ z ) ) ) -> S =/= z )

  proof
    cK
    chlt
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
    cS
    cA
    wcel
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    vz
    cv
    #
    cA
    wcel
    #
    cP
    @7
    c.or
    co
    cS
    @7
    c.or
    co
    wceq
    #
    wa
    #
    w3a
    #
    cK
    clc
    wcel
    #
    @1
    @4
    @8
    cP
    cS
    wne
    #
    @9
    cS
    @7
    wne
    @11
    @0
    @12
    @0
    @1
    @2
    @6
    @10
    simp11
    #
    cK
    hlcvl
    syl
    @0
    @1
    @2
    @6
    @10
    simp12
    #
    @3
    @4
    @5
    @10
    simp2l
    #
    @3
    @6
    @8
    @9
    simp3l
    @11
    @0
    @4
    @1
    @2
    @5
    @13
    @14
    @16
    @15
    @0
    @1
    @2
    @6
    @10
    simp13
    @3
    @4
    @5
    @10
    simp2r
    @0
    @4
    @1
    @2
    w3a
    @5
    w3a
    cS
    cP
    cA
    cS
    cP
    cQ
    c.or
    cK
    c.le
    cdleme21a.l
    cdleme21a.j
    cdleme21a.a
    atnlej1
    necomd
    syl131anc
    @3
    @6
    @8
    @9
    simp3r
    @12
    @1
    @4
    @8
    w3a
    @13
    @9
    wa
    w3a
    @7
    cS
    cA
    cP
    cS
    @7
    c.or
    cK
    cdleme21a.a
    cdleme21a.j
    cvlsupr6
    necomd
    syl132anc
end
