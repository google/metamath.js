include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp121.mm"
include "simp131.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp122.mm"
include "simp132.mm"
include "latmcl.mm"
include "jca.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp32.mm"
include "latmle1.mm"
include "latmle2.mm"
include "simp33.mm"
include "3jca.mm"
include "dath2.mm"
include "syl323anc.mm"

theorem dalawlem1
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
  assume dalawlem.o: |- O = ( LPlanes ` K )


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( ( ( P .\/ Q ) .\/ R ) e. O /\ ( ( S .\/ T ) .\/ U ) e. O ) /\ ( ( -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( P .\/ Q ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( Q .\/ R ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ P ) ) /\ ( -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( S .\/ T ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( T .\/ U ) /\ -. ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( U .\/ S ) ) /\ ( ( P .\/ S ) ./\ ( Q .\/ T ) ) .<_ ( R .\/ U ) ) ) -> ( ( P .\/ Q ) ./\ ( S .\/ T ) ) .<_ ( ( ( Q .\/ R ) ./\ ( T .\/ U ) ) .\/ ( ( R .\/ P ) ./\ ( U .\/ S ) ) ) )

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
    cO
    wcel
    #
    wa
    #
    cP
    cS
    c.or
    co
    #
    cQ
    cT
    c.or
    co
    #
    c.an
    co
    #
    @10
    c.le
    wbr
    wn
    @17
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    @17
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
    @17
    @12
    c.le
    wbr
    wn
    @17
    cT
    cU
    c.or
    co
    #
    c.le
    wbr
    wn
    @17
    cU
    cS
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    #
    @17
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
    @0
    @17
    cK
    cbs
    cfv
    #
    wcel
    #
    wa
    @4
    @8
    @11
    @13
    @20
    @23
    @17
    @15
    c.le
    wbr
    #
    @17
    @16
    c.le
    wbr
    #
    @24
    w3a
    @10
    @12
    c.an
    co
    #
    @18
    @21
    c.an
    co
    #
    @19
    @22
    c.an
    co
    #
    c.or
    co
    c.le
    wbr
    @26
    @0
    @28
    @0
    @4
    @8
    @14
    @25
    simp11
    #
    @26
    cK
    clat
    wcel
    #
    @15
    @27
    wcel
    #
    @16
    @27
    wcel
    #
    @28
    @26
    @0
    @35
    @34
    cK
    hllat
    syl
    #
    @26
    @0
    @1
    @5
    @36
    @34
    @1
    @2
    @3
    @0
    @8
    @14
    @25
    simp121
    @5
    @6
    @7
    @0
    @4
    @14
    @25
    simp131
    cA
    @27
    c.or
    cK
    cP
    cS
    @27
    eqid
    #
    dalawlem.j
    dalawlem.a
    hlatjcl
    syl3anc
    #
    @26
    @0
    @2
    @6
    @37
    @34
    @1
    @2
    @3
    @0
    @8
    @14
    @25
    simp122
    @5
    @6
    @7
    @0
    @4
    @14
    @25
    simp132
    cA
    @27
    c.or
    cK
    cQ
    cT
    @39
    dalawlem.j
    dalawlem.a
    hlatjcl
    syl3anc
    #
    @27
    cK
    c.an
    @15
    @16
    @39
    dalawlem.m
    latmcl
    syl3anc
    jca
    @0
    @4
    @8
    @14
    @25
    simp12
    @0
    @4
    @8
    @14
    @25
    simp13
    @9
    @11
    @13
    @25
    simp2l
    @9
    @11
    @13
    @25
    simp2r
    @9
    @14
    @20
    @23
    @24
    simp31
    @9
    @14
    @20
    @23
    @24
    simp32
    @26
    @29
    @30
    @24
    @26
    @35
    @36
    @37
    @29
    @38
    @40
    @41
    @27
    cK
    c.le
    c.an
    @15
    @16
    @39
    dalawlem.l
    dalawlem.m
    latmle1
    syl3anc
    @26
    @35
    @36
    @37
    @30
    @38
    @40
    @41
    @27
    cK
    c.le
    c.an
    @15
    @16
    @39
    dalawlem.l
    dalawlem.m
    latmle2
    syl3anc
    @9
    @14
    @20
    @23
    @24
    simp33
    3jca
    cA
    @27
    @17
    @31
    cP
    cQ
    cR
    cS
    cT
    cU
    @32
    @33
    c.or
    cK
    c.le
    c.an
    cO
    @39
    dalawlem.l
    dalawlem.j
    dalawlem.a
    dalawlem.m
    dalawlem.o
    @31
    eqid
    @32
    eqid
    @33
    eqid
    dath2
    syl323anc
end
