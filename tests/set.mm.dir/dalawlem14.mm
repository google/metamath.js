include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "ianor.mm"
include "dalawlem13.mm"
include "3expib.mm"
include "3exp.mm"
include "dalawlem10.mm"
include "jaod.mm"
include "syl5bi.mm"
include "3imp.mm"
include "3impib.mm"

theorem dalawlem14
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


  assert |- ( ( ( K e. HL /\ -. ( ( ( P .\/ Q ) .\/ R ) e. O /\ ( -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( P .\/ Q ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( Q .\/ R ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ P ) ) ) /\ ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ U ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) -> ( ( P .\/ Q ) ./\ ( S .\/ T ) ) .<_ ( ( ( Q .\/ R ) ./\ ( T .\/ U ) ) .\/ ( ( R .\/ P ) ./\ ( U .\/ S ) ) ) )

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
    cO
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
    @1
    c.le
    wbr
    wn
    @3
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    @3
    cR
    cP
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    #
    wa
    wn
    #
    @3
    cR
    cU
    c.or
    co
    c.le
    wbr
    #
    w3a
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
    @1
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
    @5
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
    @7
    @8
    @9
    @10
    wa
    @11
    wi
    #
    @7
    @2
    wn
    #
    @6
    wn
    #
    wo
    @0
    @8
    @12
    wi
    #
    @2
    @6
    ianor
    @0
    @13
    @15
    @14
    @0
    @13
    @8
    @12
    @0
    @13
    @8
    w3a
    @9
    @10
    @11
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
    cO
    dalawlem.l
    dalawlem.j
    dalawlem.m
    dalawlem.a
    dalawlem2.o
    dalawlem13
    3expib
    3exp
    @0
    @14
    @8
    @12
    @0
    @14
    @8
    w3a
    @9
    @10
    @11
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
    dalawlem10
    3expib
    3exp
    jaod
    syl5bi
    3imp
    3impib
end
