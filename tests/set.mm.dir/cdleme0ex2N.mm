include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2rl.mm"
include "simp3.mm"
include "cdleme0ex1N.mm"
include "syl121anc.mm"
include "wb.mm"
include "clc.mm"
include "simp11l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp2ll.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp13.mm"
include "cvlsupr2.mm"
include "syl131anc.mm"
include "simp2lr.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "simp2rr.mm"
include "jca.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "3expia.mm"
include "pm5.32rd.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem cdleme0ex2N
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )

  disjoint A u
  disjoint .\/ u
  disjoint .<_ u
  disjoint P u
  disjoint Q u
  disjoint U u
  disjoint W u
  disjoint H u
  disjoint K u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q ) -> E. u e. A ( ( P .\/ u ) = ( Q .\/ u ) /\ u .<_ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    vu
    cv
    #
    c.or
    co
    cQ
    @12
    c.or
    co
    wceq
    #
    @12
    cW
    c.le
    wbr
    #
    wa
    #
    vu
    cA
    wrex
    @12
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    @14
    wa
    #
    vu
    cA
    wrex
    #
    @11
    @2
    @5
    @6
    @10
    @18
    @2
    @9
    @10
    simp1
    @2
    @5
    @8
    @10
    simp2l
    @6
    @7
    @5
    @2
    @10
    simp2rl
    #
    @2
    @9
    @10
    simp3
    vu
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    cdleme0ex1N
    syl121anc
    @11
    @15
    @17
    vu
    cA
    @11
    @12
    cA
    wcel
    #
    wa
    @14
    @13
    @16
    @11
    @20
    @14
    @13
    @16
    wb
    @11
    @20
    @14
    w3a
    #
    @13
    @12
    cP
    wne
    #
    @12
    cQ
    wne
    #
    @16
    w3a
    #
    @16
    @21
    cK
    clc
    wcel
    #
    @3
    @6
    @20
    @10
    @13
    @24
    wb
    @21
    @0
    @25
    @0
    @1
    @9
    @10
    @20
    @14
    simp11l
    cK
    hlcvl
    syl
    @11
    @20
    @3
    @14
    @3
    @4
    @8
    @2
    @10
    simp2ll
    3ad2ant1
    @11
    @20
    @6
    @14
    @19
    3ad2ant1
    @11
    @20
    @14
    simp2
    @2
    @9
    @10
    @20
    @14
    simp13
    cA
    cP
    cQ
    @12
    c.or
    cK
    c.le
    cdleme0.a
    cdleme0.l
    cdleme0.j
    cvlsupr2
    syl131anc
    @21
    @16
    @22
    @23
    wa
    #
    @16
    wa
    @24
    @21
    @26
    @16
    @21
    @22
    @23
    @21
    @14
    @4
    @22
    @11
    @20
    @14
    simp3
    #
    @11
    @20
    @4
    @14
    @3
    @4
    @8
    @2
    @10
    simp2lr
    3ad2ant1
    @12
    cP
    cW
    c.le
    nbrne2
    syl2anc
    @21
    @14
    @7
    @23
    @27
    @11
    @20
    @7
    @14
    @6
    @7
    @5
    @2
    @10
    simp2rr
    3ad2ant1
    @12
    cQ
    cW
    c.le
    nbrne2
    syl2anc
    jca
    biantrurd
    @22
    @23
    @16
    df-3an
    syl6rbbr
    bitrd
    3expia
    pm5.32rd
    rexbidva
    mpbird
end
