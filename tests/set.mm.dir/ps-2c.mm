include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "clln.mm"
include "cfv.mm"
include "cp0.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp13.mm"
include "simp31l.mm"
include "latnlej1r.mm"
include "syl131anc.mm"
include "llni2.mm"
include "syl31anc.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31r.mm"
include "simp32.mm"
include "simp33.mm"
include "ps-2b.mm"
include "syl333anc.mm"
include "2llnmat.mm"
include "syl32anc.mm"

theorem ps-2c
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume 2atm.l: |- .<_ = ( le ` K )
  assume 2atm.j: |- .\/ = ( join ` K )
  assume 2atm.m: |- ./\ = ( meet ` K )
  assume 2atm.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( ( -. P .<_ ( Q .\/ R ) /\ S =/= T ) /\ ( P .\/ R ) =/= ( S .\/ T ) /\ ( S .<_ ( P .\/ Q ) /\ T .<_ ( Q .\/ R ) ) ) ) -> ( ( P .\/ R ) ./\ ( S .\/ T ) ) e. A )

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
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    cT
    wne
    #
    wa
    #
    cP
    cR
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    cT
    @8
    c.le
    wbr
    wa
    #
    w3a
    #
    w3a
    #
    @0
    @12
    cK
    clln
    cfv
    #
    wcel
    #
    @13
    @18
    wcel
    #
    @14
    @12
    @13
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    wne
    #
    @21
    cA
    wcel
    @0
    @1
    @2
    @7
    @16
    simp11
    #
    @17
    @0
    @1
    @4
    cP
    cR
    wne
    #
    @19
    @24
    @0
    @1
    @2
    @7
    @16
    simp12
    #
    @3
    @4
    @5
    @6
    @16
    simp21
    #
    @17
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @29
    wcel
    #
    cR
    @29
    wcel
    #
    @9
    @25
    @17
    @0
    @28
    @24
    cK
    hllat
    syl
    @17
    @1
    @30
    @26
    cA
    @29
    cP
    cK
    @29
    eqid
    #
    2atm.a
    atbase
    syl
    @17
    @2
    @31
    @0
    @1
    @2
    @7
    @16
    simp13
    #
    cA
    @29
    cQ
    cK
    @33
    2atm.a
    atbase
    syl
    @17
    @4
    @32
    @27
    cA
    @29
    cR
    cK
    @33
    2atm.a
    atbase
    syl
    @9
    @10
    @14
    @15
    @3
    @7
    simp31l
    #
    @29
    c.or
    cK
    c.le
    cP
    cQ
    cR
    @33
    2atm.l
    2atm.j
    latnlej1r
    syl131anc
    cA
    cP
    cR
    c.or
    cK
    @18
    2atm.j
    2atm.a
    @18
    eqid
    #
    llni2
    syl31anc
    @17
    @0
    @5
    @6
    @10
    @20
    @24
    @3
    @4
    @5
    @6
    @16
    simp22
    #
    @3
    @4
    @5
    @6
    @16
    simp23
    #
    @9
    @10
    @14
    @15
    @3
    @7
    simp31r
    #
    cA
    cS
    cT
    c.or
    cK
    @18
    2atm.j
    2atm.a
    @36
    llni2
    syl31anc
    @3
    @7
    @11
    @14
    @15
    simp32
    @17
    @0
    @1
    @2
    @4
    @5
    @6
    @9
    @10
    @15
    @23
    @24
    @26
    @34
    @27
    @37
    @38
    @35
    @39
    @3
    @7
    @11
    @14
    @15
    simp33
    cA
    cP
    cQ
    cR
    cS
    cT
    c.or
    cK
    c.le
    c.an
    @22
    2atm.l
    2atm.j
    2atm.m
    @22
    eqid
    #
    2atm.a
    ps-2b
    syl333anc
    cA
    cK
    c.an
    @18
    @12
    @13
    @22
    2atm.m
    @40
    2atm.a
    @36
    2llnmat
    syl32anc
end
