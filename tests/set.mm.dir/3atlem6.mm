include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "simp11.mm"
include "simp121.mm"
include "simp122.mm"
include "simp123.mm"
include "hlatj32.mm"
include "syl13anc.mm"
include "3jca.mm"
include "simp13.mm"
include "simp21.mm"
include "wi.mm"
include "simp22.mm"
include "necomd.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "mtod.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latnlej1l.mm"
include "simp23.mm"
include "wb.mm"
include "simp133.mm"
include "hlatexchb1.mm"
include "mpbid.mm"
include "breq2d.mm"
include "mtbid.mm"
include "simp3.mm"
include "eqbrtrrd.mm"
include "3atlem5.mm"
include "syl331anc.mm"
include "eqtrd.mm"

theorem 3atlem6
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
  assume 3at.l: |- .<_ = ( le ` K )
  assume 3at.j: |- .\/ = ( join ` K )
  assume 3at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ P =/= Q /\ Q .<_ ( P .\/ U ) ) /\ ( ( P .\/ Q ) .\/ R ) .<_ ( ( S .\/ T ) .\/ U ) ) -> ( ( P .\/ Q ) .\/ R ) = ( ( S .\/ T ) .\/ U ) )

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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cP
    cQ
    wne
    #
    cQ
    cP
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    @10
    cR
    c.or
    co
    #
    cS
    cT
    c.or
    co
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    @17
    cP
    cR
    c.or
    co
    #
    cQ
    c.or
    co
    #
    @18
    @20
    @0
    @1
    @2
    @3
    @17
    @22
    wceq
    @0
    @4
    @8
    @16
    @19
    simp11
    #
    @1
    @2
    @3
    @0
    @8
    @16
    @19
    simp121
    #
    @1
    @2
    @3
    @0
    @8
    @16
    @19
    simp122
    #
    @1
    @2
    @3
    @0
    @8
    @16
    @19
    simp123
    #
    cA
    cP
    cQ
    cR
    c.or
    cK
    3at.j
    3at.a
    hlatj32
    syl13anc
    #
    @20
    @0
    @1
    @3
    @2
    w3a
    @8
    cQ
    @21
    c.le
    wbr
    #
    wn
    cP
    cR
    wne
    #
    cR
    @14
    c.le
    wbr
    #
    wn
    @22
    @18
    c.le
    wbr
    @22
    @18
    wceq
    @23
    @20
    @1
    @3
    @2
    @24
    @26
    @25
    3jca
    @0
    @4
    @8
    @16
    @19
    simp13
    @20
    @28
    @11
    @9
    @12
    @13
    @15
    @19
    simp21
    #
    @20
    @0
    @2
    @3
    @1
    cQ
    cP
    wne
    #
    @28
    @11
    wi
    @23
    @25
    @26
    @24
    @20
    cP
    cQ
    @9
    @12
    @13
    @15
    @19
    simp22
    necomd
    #
    cA
    cQ
    cR
    cP
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    hlatexch1
    syl131anc
    mtod
    @20
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @35
    wcel
    #
    cQ
    @35
    wcel
    #
    @12
    @29
    @20
    @0
    @34
    @23
    cK
    hllat
    syl
    @20
    @3
    @36
    @26
    cA
    @35
    cR
    cK
    @35
    eqid
    #
    3at.a
    atbase
    syl
    @20
    @1
    @37
    @24
    cA
    @35
    cP
    cK
    @39
    3at.a
    atbase
    syl
    @20
    @2
    @38
    @25
    cA
    @35
    cQ
    cK
    @39
    3at.a
    atbase
    syl
    @31
    @34
    @36
    @37
    @38
    w3a
    @12
    w3a
    cR
    cP
    @35
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @39
    3at.l
    3at.j
    latnlej1l
    necomd
    syl131anc
    @20
    @11
    @30
    @31
    @20
    @10
    @14
    cR
    c.le
    @20
    @15
    @10
    @14
    wceq
    #
    @9
    @12
    @13
    @15
    @19
    simp23
    @20
    @0
    @2
    @7
    @1
    @32
    @15
    @40
    wb
    @23
    @25
    @5
    @6
    @7
    @0
    @4
    @16
    @19
    simp133
    @24
    @33
    cA
    cQ
    cU
    cP
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    hlatexchb1
    syl131anc
    mpbid
    breq2d
    mtbid
    @20
    @17
    @22
    @18
    c.le
    @27
    @9
    @16
    @19
    simp3
    eqbrtrrd
    cA
    cP
    cR
    cQ
    cS
    cT
    cU
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem5
    syl331anc
    eqtrd
end
