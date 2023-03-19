include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp11.mm"
include "simp122.mm"
include "simp123.mm"
include "simp121.mm"
include "3jca.mm"
include "simp132.mm"
include "simp133.mm"
include "simp131.mm"
include "wceq.mm"
include "simp11l.mm"
include "hlatjrot.mm"
include "syl13anc.mm"
include "simp2l.mm"
include "eqeltrd.mm"
include "simp2r.mm"
include "simp312.mm"
include "simp313.mm"
include "simp311.mm"
include "simp322.mm"
include "simp323.mm"
include "simp321.mm"
include "simp332.mm"
include "simp333.mm"
include "simp331.mm"
include "dath.mm"
include "syl323anc.mm"

theorem dath2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  assume dathb.b: |- B = ( Base ` K )
  assume dathb.l: |- .<_ = ( le ` K )
  assume dathb.j: |- .\/ = ( join ` K )
  assume dathb.a: |- A = ( Atoms ` K )
  assume dathb.m: |- ./\ = ( meet ` K )
  assume dathb.o: |- O = ( LPlanes ` K )
  assume dathb.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dathb.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dathb.f: |- F = ( ( R .\/ P ) ./\ ( U .\/ S ) )


  assert |- ( ( ( ( K e. HL /\ C e. B ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( ( ( P .\/ Q ) .\/ R ) e. O /\ ( ( S .\/ T ) .\/ U ) e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) -> D .<_ ( E .\/ F ) )

  proof
    cK
    chlt
    wcel
    #
    cC
    cB
    wcel
    #
    wa
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
    #
    cT
    cA
    wcel
    #
    cU
    cA
    wcel
    #
    w3a
    #
    w3a
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
    cS
    cT
    c.or
    co
    #
    cU
    c.or
    co
    #
    cO
    wcel
    #
    wa
    #
    cC
    @12
    c.le
    wbr
    wn
    #
    cC
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cC
    cR
    cP
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    cC
    @15
    c.le
    wbr
    wn
    #
    cC
    cT
    cU
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cC
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    cC
    cP
    cS
    c.or
    co
    c.le
    wbr
    #
    cC
    cQ
    cT
    c.or
    co
    c.le
    wbr
    #
    cC
    cR
    cU
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    w3a
    #
    @2
    @4
    @5
    @3
    w3a
    @8
    @9
    @7
    w3a
    @20
    cP
    c.or
    co
    #
    cO
    wcel
    @25
    cS
    c.or
    co
    #
    cO
    wcel
    @21
    @22
    @19
    w3a
    @26
    @27
    @24
    w3a
    @30
    @31
    @29
    w3a
    cD
    cE
    cF
    c.or
    co
    c.le
    wbr
    @2
    @6
    @10
    @18
    @33
    simp11
    @34
    @4
    @5
    @3
    @3
    @4
    @5
    @2
    @10
    @18
    @33
    simp122
    #
    @3
    @4
    @5
    @2
    @10
    @18
    @33
    simp123
    #
    @3
    @4
    @5
    @2
    @10
    @18
    @33
    simp121
    #
    3jca
    @34
    @8
    @9
    @7
    @7
    @8
    @9
    @2
    @6
    @18
    @33
    simp132
    #
    @7
    @8
    @9
    @2
    @6
    @18
    @33
    simp133
    #
    @7
    @8
    @9
    @2
    @6
    @18
    @33
    simp131
    #
    3jca
    @34
    @35
    @13
    cO
    @34
    @0
    @4
    @5
    @3
    @35
    @13
    wceq
    @0
    @1
    @6
    @10
    @18
    @33
    simp11l
    #
    @37
    @38
    @39
    cA
    cQ
    cR
    cP
    c.or
    cK
    dathb.j
    dathb.a
    hlatjrot
    syl13anc
    @11
    @14
    @17
    @33
    simp2l
    eqeltrd
    @34
    @36
    @16
    cO
    @34
    @0
    @8
    @9
    @7
    @36
    @16
    wceq
    @43
    @40
    @41
    @42
    cA
    cT
    cU
    cS
    c.or
    cK
    dathb.j
    dathb.a
    hlatjrot
    syl13anc
    @11
    @14
    @17
    @33
    simp2r
    eqeltrd
    @34
    @21
    @22
    @19
    @19
    @21
    @22
    @28
    @32
    @11
    @18
    simp312
    @19
    @21
    @22
    @28
    @32
    @11
    @18
    simp313
    @19
    @21
    @22
    @28
    @32
    @11
    @18
    simp311
    3jca
    @34
    @26
    @27
    @24
    @24
    @26
    @27
    @23
    @32
    @11
    @18
    simp322
    @24
    @26
    @27
    @23
    @32
    @11
    @18
    simp323
    @24
    @26
    @27
    @23
    @32
    @11
    @18
    simp321
    3jca
    @34
    @30
    @31
    @29
    @29
    @30
    @31
    @23
    @28
    @11
    @18
    simp332
    @29
    @30
    @31
    @23
    @28
    @11
    @18
    simp333
    @29
    @30
    @31
    @23
    @28
    @11
    @18
    simp331
    3jca
    cA
    cB
    cC
    cE
    cQ
    cR
    cP
    cT
    cU
    cS
    cF
    cD
    c.or
    cK
    c.le
    c.an
    cO
    dathb.b
    dathb.l
    dathb.j
    dathb.a
    dathb.m
    dathb.o
    dathb.e
    dathb.f
    dathb.d
    dath
    syl323anc
end
