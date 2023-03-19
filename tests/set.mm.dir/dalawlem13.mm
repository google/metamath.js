include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "wn.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "simp11.mm"
include "simp12.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "simp22.mm"
include "simp23.mm"
include "simp21.mm"
include "islpln2a.mm"
include "syl13anc.mm"
include "df-ne.mm"
include "anbi1i.mm"
include "pm4.56.mm"
include "bitri.mm"
include "syl6rbb.mm"
include "hlatjrot.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "con1bid.mm"
include "mpbid.mm"
include "simp13.mm"
include "simp2.mm"
include "simp3.mm"
include "wi.mm"
include "dalawlem12.mm"
include "3expib.mm"
include "3exp.mm"
include "dalawlem11.mm"
include "jaod.mm"
include "3imp.mm"
include "3impib.mm"
include "syl311anc.mm"

theorem dalawlem13
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  assume dalawlem.l: |- .<_ = ( le ` K )
  assume dalawlem.j: |- .\/ = ( join ` K )
  assume dalawlem.m: |- ./\ = ( meet ` K )
  assume dalawlem.a: |- A = ( Atoms ` K )
  assume dalawlem2.o: |- O = ( LPlanes ` K )


  assert |- ( ( ( K e. HL /\ -. ( ( P .\/ Q ) .\/ R ) e. O /\ ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ U ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) -> ( ( P .\/ Q ) ./\ ( S .\/ T ) ) .<_ ( ( ( Q .\/ R ) ./\ ( T .\/ U ) ) .\/ ( ( R .\/ P ) ./\ ( U .\/ S ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    cO
    wcel
    #
    wn
    #
    cP
    cS
    c.or
    co
    cQ
    cT
    c.or
    co
    c.an
    co
    cR
    cU
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cS
    cA
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    w3a
    #
    w3a
    #
    @0
    cQ
    cR
    wceq
    #
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wo
    #
    @5
    @10
    @11
    @1
    cS
    cT
    c.or
    co
    c.an
    co
    @14
    cT
    cU
    c.or
    co
    c.an
    co
    cR
    cP
    c.or
    co
    cU
    cS
    c.or
    co
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
    @0
    @4
    @5
    @10
    @11
    simp11
    #
    @12
    @4
    @16
    @0
    @4
    @5
    @10
    @11
    simp12
    @12
    @16
    @3
    @12
    @16
    wn
    #
    @14
    cP
    c.or
    co
    #
    cO
    wcel
    #
    @3
    @12
    @21
    cQ
    cR
    wne
    #
    @15
    wn
    #
    wa
    #
    @19
    @12
    @0
    @8
    @9
    @7
    @21
    @24
    wb
    @18
    @6
    @7
    @8
    @9
    @11
    simp22
    #
    @6
    @7
    @8
    @9
    @11
    simp23
    #
    @6
    @7
    @8
    @9
    @11
    simp21
    #
    cA
    cO
    cQ
    cR
    cP
    c.or
    cK
    c.le
    dalawlem.l
    dalawlem.j
    dalawlem.a
    dalawlem2.o
    islpln2a
    syl13anc
    @24
    @13
    wn
    #
    @23
    wa
    @19
    @22
    @28
    @23
    cQ
    cR
    df-ne
    anbi1i
    @13
    @15
    pm4.56
    bitri
    syl6rbb
    @12
    @20
    @2
    cO
    @12
    @0
    @8
    @9
    @7
    @20
    @2
    wceq
    @18
    @25
    @26
    @27
    cA
    cQ
    cR
    cP
    c.or
    cK
    dalawlem.j
    dalawlem.a
    hlatjrot
    syl13anc
    eleq1d
    bitrd
    con1bid
    mpbid
    @0
    @4
    @5
    @10
    @11
    simp13
    @6
    @10
    @11
    simp2
    @6
    @10
    @11
    simp3
    @0
    @16
    @5
    w3a
    @10
    @11
    @17
    @0
    @16
    @5
    @10
    @11
    wa
    @17
    wi
    #
    @0
    @13
    @5
    @29
    wi
    @15
    @0
    @13
    @5
    @29
    @0
    @13
    @5
    w3a
    @10
    @11
    @17
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    c.an
    dalawlem.l
    dalawlem.j
    dalawlem.m
    dalawlem.a
    dalawlem12
    3expib
    3exp
    @0
    @15
    @5
    @29
    @0
    @15
    @5
    w3a
    @10
    @11
    @17
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    c.an
    dalawlem.l
    dalawlem.j
    dalawlem.m
    dalawlem.a
    dalawlem11
    3expib
    3exp
    jaod
    3imp
    3impib
    syl311anc
end
