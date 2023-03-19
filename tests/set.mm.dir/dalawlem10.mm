include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "w3o.mm"
include "simp11.mm"
include "simp12.mm"
include "3oran.mm"
include "sylibr.mm"
include "simp13.mm"
include "simp2.mm"
include "simp3.mm"
include "wa.mm"
include "wi.mm"
include "dalawlem5.mm"
include "3expib.mm"
include "3exp.mm"
include "dalawlem8.mm"
include "dalawlem9.mm"
include "3jaod.mm"
include "3imp.mm"
include "3impib.mm"
include "syl311anc.mm"

theorem dalawlem10
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
  assume dalawlem.l: |- .<_ = ( le ` K )
  assume dalawlem.j: |- .\/ = ( join ` K )
  assume dalawlem.m: |- ./\ = ( meet ` K )
  assume dalawlem.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ -. ( -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( P .\/ Q ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( Q .\/ R ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ P ) ) /\ ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ U ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) -> ( ( P .\/ Q ) ./\ ( S .\/ T ) ) .<_ ( ( ( Q .\/ R ) ./\ ( T .\/ U ) ) .\/ ( ( R .\/ P ) ./\ ( U .\/ S ) ) ) )

  proof
    cK
    chlt
    wcel
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
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @1
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @1
    cR
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    w3a
    wn
    #
    @1
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
    cQ
    cA
    wcel
    cR
    cA
    wcel
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
    @3
    @5
    @7
    w3o
    #
    @9
    @11
    @12
    @2
    cS
    cT
    c.or
    co
    c.an
    co
    @4
    cT
    cU
    c.or
    co
    c.an
    co
    @6
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
    @8
    @9
    @11
    @12
    simp11
    @13
    @8
    @14
    @0
    @8
    @9
    @11
    @12
    simp12
    @3
    @5
    @7
    3oran
    sylibr
    @0
    @8
    @9
    @11
    @12
    simp13
    @10
    @11
    @12
    simp2
    @10
    @11
    @12
    simp3
    @0
    @14
    @9
    w3a
    @11
    @12
    @15
    @0
    @14
    @9
    @11
    @12
    wa
    @15
    wi
    #
    @0
    @3
    @9
    @16
    wi
    @5
    @7
    @0
    @3
    @9
    @16
    @0
    @3
    @9
    w3a
    @11
    @12
    @15
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
    dalawlem5
    3expib
    3exp
    @0
    @5
    @9
    @16
    @0
    @5
    @9
    w3a
    @11
    @12
    @15
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
    dalawlem8
    3expib
    3exp
    @0
    @7
    @9
    @16
    @0
    @7
    @9
    w3a
    @11
    @12
    @15
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
    dalawlem9
    3expib
    3exp
    3jaod
    3imp
    3impib
    syl311anc
end
