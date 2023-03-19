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
include "wi.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp1l3.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breqtrrd.mm"
include "3jca.mm"
include "3exp.mm"
include "reximdvai.mm"

theorem atbtwnex
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
  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( X e. B /\ P .<_ X /\ -. Q .<_ X ) ) -> E. r e. A ( r =/= Q /\ -. r .<_ X /\ P .<_ ( Q .\/ r ) ) )

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
    @9
    cQ
    wne
    #
    @9
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
    @11
    @9
    cX
    c.le
    wbr
    wn
    #
    cP
    cQ
    @9
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vr
    cA
    wrex
    @3
    @7
    cP
    cQ
    wne
    #
    @14
    @8
    @5
    @6
    @19
    @3
    @4
    @5
    @6
    simpr2
    @3
    @4
    @5
    @6
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
    @8
    @13
    @18
    vr
    cA
    @8
    @9
    cA
    wcel
    #
    @13
    @18
    @8
    @20
    @13
    w3a
    #
    @11
    @15
    @17
    @8
    @20
    @10
    @11
    @12
    simp32
    #
    @21
    @10
    @15
    @8
    @20
    @10
    @11
    @12
    simp31
    @21
    @3
    @20
    @4
    @5
    @6
    @12
    @10
    @15
    wb
    @3
    @7
    @20
    @13
    simp1l
    @8
    @20
    @13
    simp2
    #
    @4
    @5
    @6
    @3
    @20
    @13
    simp1r1
    @4
    @5
    @6
    @3
    @20
    @13
    simp1r2
    @4
    @5
    @6
    @3
    @20
    @13
    simp1r3
    @8
    @20
    @10
    @11
    @12
    simp33
    #
    cA
    cB
    cP
    cQ
    @9
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
    @21
    cP
    @9
    cQ
    c.or
    co
    #
    @16
    c.le
    @21
    @12
    cP
    @25
    c.le
    wbr
    #
    @24
    @21
    @0
    @20
    @1
    @2
    @11
    @12
    @26
    wi
    @0
    @1
    @2
    @7
    @20
    @13
    simp1l1
    #
    @23
    @0
    @1
    @2
    @7
    @20
    @13
    simp1l2
    @0
    @1
    @2
    @7
    @20
    @13
    simp1l3
    #
    @22
    cA
    @9
    cP
    cQ
    c.or
    cK
    c.le
    atbtwn.l
    atbtwn.j
    atbtwn.a
    hlatexch2
    syl131anc
    mpd
    @21
    @0
    @2
    @20
    @16
    @25
    wceq
    @27
    @28
    @23
    cA
    c.or
    cK
    cQ
    @9
    atbtwn.j
    atbtwn.a
    hlatjcom
    syl3anc
    breqtrrd
    3jca
    3exp
    reximdvai
    mpd
end
