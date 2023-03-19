include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wrex.mm"
include "simpr2.mm"
include "simpr3.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "hlsupr.mm"
include "syldan.mm"
include "simp32.mm"
include "simp31.mm"
include "wb.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp1r1.mm"
include "simp1r2.mm"
include "simp1r3.mm"
include "simp33.mm"
include "atbtwn.mm"
include "syl123anc.mm"
include "mpbid.mm"
include "3jca.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem atbtwnexOLDN
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vr: setvar r
  assume atbtwn.b: |- B = ( Base ` K )
  assume atbtwn.l: |- .<_ = ( le ` K )
  assume atbtwn.j: |- .\/ = ( join ` K )
  assume atbtwn.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint B r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint X r
  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( X e. B /\ P .<_ X /\ -. Q .<_ X ) ) -> E. r e. A ( r =/= Q /\ -. r .<_ X /\ r .<_ ( P .\/ Q ) ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    w3a
    #
    cX
    cB
    wcel
    #
    cP
    cX
    c.le
    wbr
    #
    cQ
    cX
    c.le
    wbr
    wn
    #
    w3a
    #
    wa
    #
    vr
    cv
    #
    cP
    wne
    #
    @6
    cQ
    wne
    #
    @6
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    vr
    cA
    wrex
    #
    @8
    @6
    cX
    c.le
    wbr
    wn
    #
    @9
    w3a
    #
    vr
    cA
    wrex
    @0
    @4
    cP
    cQ
    wne
    #
    @11
    @5
    @2
    @3
    @14
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    cP
    cQ
    cX
    c.le
    nbrne2
    syl2anc
    cA
    cP
    cQ
    c.or
    cK
    c.le
    vr
    atbtwn.l
    atbtwn.j
    atbtwn.a
    hlsupr
    syldan
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
    @10
    @13
    @5
    @15
    @10
    w3a
    #
    @8
    @12
    @9
    @5
    @15
    @7
    @8
    @9
    simp32
    @16
    @7
    @12
    @5
    @15
    @7
    @8
    @9
    simp31
    @16
    @0
    @15
    @1
    @2
    @3
    @9
    @7
    @12
    wb
    @0
    @4
    @15
    @10
    simp1l
    @5
    @15
    @10
    simp2
    @1
    @2
    @3
    @0
    @15
    @10
    simp1r1
    @1
    @2
    @3
    @0
    @15
    @10
    simp1r2
    @1
    @2
    @3
    @0
    @15
    @10
    simp1r3
    @5
    @15
    @7
    @8
    @9
    simp33
    #
    cA
    cB
    cP
    cQ
    @6
    c.or
    cK
    c.le
    cX
    atbtwn.b
    atbtwn.l
    atbtwn.j
    atbtwn.a
    atbtwn
    syl123anc
    mpbid
    @17
    3jca
    3exp
    reximdvai
    mpd
end
