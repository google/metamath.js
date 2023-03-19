include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "clpl.mm"
include "cfv.mm"
include "wn.mm"
include "wa.mm"
include "eqid.mm"
include "dalawlem14.mm"
include "3expib.mm"
include "3exp.mm"
include "dalawlem15.mm"
include "simp11.mm"
include "simp2.mm"
include "simp3.mm"
include "simp2ll.mm"
include "3ad2ant1.mm"
include "simp2rl.mm"
include "simp2lr.mm"
include "simp2rr.mm"
include "simp13.mm"
include "dalawlem1.mm"
include "syl323anc.mm"
include "ecased.mm"
include "exp4a.mm"
include "com34.mm"
include "com24.mm"
include "3imp.mm"

theorem dalaw
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
  assume dalaw.l: |- .<_ = ( le ` K )
  assume dalaw.j: |- .\/ = ( join ` K )
  assume dalaw.m: |- ./\ = ( meet ` K )
  assume dalaw.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) -> ( ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ U ) -> ( ( P .\/ Q ) ./\ ( S .\/ T ) ) .<_ ( ( ( Q .\/ R ) ./\ ( T .\/ U ) ) .\/ ( ( R .\/ P ) ./\ ( U .\/ S ) ) ) ) )

  proof
    cK
    chlt
    wcel
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
    cR
    cU
    c.or
    co
    c.le
    wbr
    #
    cP
    cQ
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    c.an
    co
    cQ
    cR
    c.or
    co
    #
    cT
    cU
    c.or
    co
    #
    c.an
    co
    cR
    cP
    c.or
    co
    #
    cU
    cS
    c.or
    co
    #
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
    wi
    @0
    @4
    @2
    @1
    @11
    @0
    @4
    @1
    @2
    @11
    @0
    @4
    @1
    @2
    @11
    @0
    @5
    cR
    c.or
    co
    cK
    clpl
    cfv
    #
    wcel
    #
    @3
    @5
    c.le
    wbr
    wn
    @3
    @7
    c.le
    wbr
    wn
    @3
    @9
    c.le
    wbr
    wn
    w3a
    #
    wa
    #
    @6
    cU
    c.or
    co
    @12
    wcel
    #
    @3
    @6
    c.le
    wbr
    wn
    @3
    @8
    c.le
    wbr
    wn
    @3
    @10
    c.le
    wbr
    wn
    w3a
    #
    wa
    #
    @4
    @1
    @2
    wa
    @11
    wi
    #
    wi
    @0
    @15
    wn
    #
    @4
    @19
    @0
    @20
    @4
    w3a
    @1
    @2
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
    @12
    dalaw.l
    dalaw.j
    dalaw.m
    dalaw.a
    @12
    eqid
    #
    dalawlem14
    3expib
    3exp
    @0
    @18
    wn
    #
    @4
    @19
    @0
    @22
    @4
    w3a
    @1
    @2
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
    @12
    dalaw.l
    dalaw.j
    dalaw.m
    dalaw.a
    @21
    dalawlem15
    3expib
    3exp
    @0
    @15
    @18
    wa
    #
    @4
    @19
    @0
    @23
    @4
    w3a
    #
    @1
    @2
    @11
    @24
    @1
    @2
    w3a
    @0
    @1
    @2
    @13
    @16
    @14
    @17
    @4
    @11
    @0
    @23
    @4
    @1
    @2
    simp11
    @24
    @1
    @2
    simp2
    @24
    @1
    @2
    simp3
    @24
    @1
    @13
    @2
    @13
    @14
    @18
    @0
    @4
    simp2ll
    3ad2ant1
    @24
    @1
    @16
    @2
    @16
    @17
    @15
    @0
    @4
    simp2rl
    3ad2ant1
    @24
    @1
    @14
    @2
    @13
    @14
    @18
    @0
    @4
    simp2lr
    3ad2ant1
    @24
    @1
    @17
    @2
    @16
    @17
    @15
    @0
    @4
    simp2rr
    3ad2ant1
    @0
    @23
    @4
    @1
    @2
    simp13
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
    @12
    dalaw.l
    dalaw.j
    dalaw.m
    dalaw.a
    @21
    dalawlem1
    syl323anc
    3expib
    3exp
    ecased
    exp4a
    com34
    com24
    3imp
end
