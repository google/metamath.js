include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wne.mm"
include "wceq.mm"
include "simp31.mm"
include "simp32.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "wb.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp23.mm"
include "eqid.mm"
include "atbase.mm"
include "simp12.mm"
include "simp13.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp21.mm"
include "simp22.mm"
include "hlatjcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "cp0.mm"
include "latmcl.mm"
include "atlen0.mm"
include "syl31anc.mm"
include "neneqd.mm"
include "wo.mm"
include "simp33.mm"
include "2atmat0.mm"
include "syl33anc.mm"
include "ord.mm"
include "mt3d.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem 2atm
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


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( T .<_ ( P .\/ Q ) /\ T .<_ ( R .\/ S ) /\ ( P .\/ Q ) =/= ( R .\/ S ) ) ) -> T = ( ( P .\/ Q ) ./\ ( R .\/ S ) ) )

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
    cT
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cT
    cR
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @8
    @10
    wne
    #
    w3a
    #
    w3a
    #
    cT
    @8
    @10
    c.an
    co
    #
    c.le
    wbr
    #
    cT
    @15
    wceq
    #
    @14
    @9
    @11
    @16
    @3
    @7
    @9
    @11
    @12
    simp31
    @3
    @7
    @9
    @11
    @12
    simp32
    @14
    cK
    clat
    wcel
    #
    cT
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    @19
    wcel
    #
    @10
    @19
    wcel
    #
    @9
    @11
    wa
    @16
    wb
    @14
    @0
    @18
    @0
    @1
    @2
    @7
    @13
    simp11
    #
    cK
    hllat
    syl
    #
    @14
    @6
    @20
    @3
    @4
    @5
    @6
    @13
    simp23
    #
    cA
    @19
    cT
    cK
    @19
    eqid
    #
    2atm.a
    atbase
    syl
    @14
    @18
    cP
    @19
    wcel
    #
    cQ
    @19
    wcel
    #
    @21
    @24
    @14
    @1
    @27
    @0
    @1
    @2
    @7
    @13
    simp12
    #
    cA
    @19
    cP
    cK
    @26
    2atm.a
    atbase
    syl
    @14
    @2
    @28
    @0
    @1
    @2
    @7
    @13
    simp13
    #
    cA
    @19
    cQ
    cK
    @26
    2atm.a
    atbase
    syl
    @19
    c.or
    cK
    cP
    cQ
    @26
    2atm.j
    latjcl
    syl3anc
    #
    @14
    @0
    @4
    @5
    @22
    @23
    @3
    @4
    @5
    @6
    @13
    simp21
    #
    @3
    @4
    @5
    @6
    @13
    simp22
    #
    cA
    @19
    c.or
    cK
    cR
    cS
    @26
    2atm.j
    2atm.a
    hlatjcl
    syl3anc
    #
    @19
    cK
    c.le
    c.an
    cT
    @8
    @10
    @26
    2atm.l
    2atm.m
    latlem12
    syl13anc
    mpbi2and
    #
    @14
    cK
    cal
    wcel
    #
    @6
    @15
    cA
    wcel
    #
    @16
    @17
    wb
    @14
    @0
    @36
    @23
    cK
    hlatl
    syl
    #
    @25
    @14
    @37
    @15
    cK
    cp0
    cfv
    #
    wceq
    #
    @14
    @15
    @39
    @14
    @36
    @15
    @19
    wcel
    #
    @6
    @16
    @15
    @39
    wne
    @38
    @14
    @18
    @21
    @22
    @41
    @24
    @31
    @34
    @19
    cK
    c.an
    @8
    @10
    @26
    2atm.m
    latmcl
    syl3anc
    @25
    @35
    cA
    @19
    cT
    cK
    c.le
    @15
    @39
    @26
    2atm.l
    @39
    eqid
    #
    2atm.a
    atlen0
    syl31anc
    neneqd
    @14
    @37
    @40
    @14
    @0
    @1
    @2
    @4
    @5
    @12
    @37
    @40
    wo
    @23
    @29
    @30
    @32
    @33
    @3
    @7
    @9
    @11
    @12
    simp33
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.an
    @39
    2atm.j
    2atm.m
    @42
    2atm.a
    2atmat0
    syl33anc
    ord
    mt3d
    cA
    cT
    @15
    cK
    c.le
    2atm.l
    2atm.a
    atcmp
    syl3anc
    mpbid
end
