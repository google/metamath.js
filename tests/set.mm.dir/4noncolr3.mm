include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp12.mm"
include "simp13.mm"
include "simp32.mm"
include "latnlej1r.mm"
include "syl131anc.mm"
include "necomd.mm"
include "simp2r.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp33.mm"
include "wceq.mm"
include "hlatjass.mm"
include "syl13anc.mm"
include "breq2d.mm"
include "mtbid.mm"
include "latnlej2r.mm"
include "wi.mm"
include "simp31.mm"
include "hlatexch1.mm"
include "latjcom.mm"
include "sylibrd.mm"
include "mtod.mm"
include "hlexch1.mm"
include "oveq1d.mm"
include "latj31.mm"
include "eqtrd.mm"
include "sylibd.mm"
include "3jca.mm"

theorem 4noncolr3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3noncol.l: |- .<_ = ( le ` K )
  assume 3noncol.j: |- .\/ = ( join ` K )
  assume 3noncol.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( Q =/= R /\ -. S .<_ ( Q .\/ R ) /\ -. P .<_ ( ( Q .\/ R ) .\/ S ) ) )

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
    wa
    #
    cP
    cQ
    wne
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
    cS
    @8
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    cQ
    cR
    wne
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cP
    @16
    cS
    c.or
    co
    c.le
    wbr
    #
    wn
    @15
    cR
    cQ
    @15
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
    @20
    wcel
    #
    cQ
    @20
    wcel
    #
    @10
    cR
    cQ
    wne
    @15
    @0
    @19
    @0
    @1
    @2
    @6
    @14
    simp11
    #
    cK
    hllat
    syl
    #
    @15
    @4
    @21
    @3
    @4
    @5
    @14
    simp2l
    #
    cA
    @20
    cR
    cK
    @20
    eqid
    #
    3noncol.a
    atbase
    syl
    #
    @15
    @1
    @22
    @0
    @1
    @2
    @6
    @14
    simp12
    #
    cA
    @20
    cP
    cK
    @27
    3noncol.a
    atbase
    syl
    #
    @15
    @2
    @23
    @0
    @1
    @2
    @6
    @14
    simp13
    #
    cA
    @20
    cQ
    cK
    @27
    3noncol.a
    atbase
    syl
    #
    @3
    @6
    @7
    @10
    @13
    simp32
    #
    @20
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @27
    3noncol.l
    3noncol.j
    latnlej1r
    syl131anc
    necomd
    @15
    @19
    cS
    @20
    wcel
    #
    @22
    @16
    @20
    wcel
    #
    cS
    cP
    @16
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @17
    @25
    @15
    @5
    @34
    @3
    @4
    @5
    @14
    simp2r
    #
    cA
    @20
    cS
    cK
    @27
    3noncol.a
    atbase
    syl
    @30
    @15
    @19
    @23
    @21
    @35
    @25
    @32
    @28
    @20
    c.or
    cK
    cQ
    cR
    @27
    3noncol.j
    latjcl
    syl3anc
    #
    @15
    @12
    @37
    @3
    @6
    @7
    @10
    @13
    simp33
    #
    @15
    @11
    @36
    cS
    c.le
    @15
    @0
    @1
    @2
    @4
    @11
    @36
    wceq
    @24
    @29
    @31
    @26
    cA
    cP
    cQ
    cR
    c.or
    cK
    3noncol.j
    3noncol.a
    hlatjass
    syl13anc
    breq2d
    mtbid
    @20
    c.or
    cK
    c.le
    cS
    cP
    @16
    @27
    3noncol.l
    3noncol.j
    latnlej2r
    syl131anc
    @15
    @18
    @12
    @40
    @15
    @18
    cS
    @16
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @12
    @15
    @0
    @1
    @5
    @35
    cP
    @16
    c.le
    wbr
    #
    wn
    @18
    @42
    wi
    @24
    @29
    @38
    @39
    @15
    @43
    @9
    @33
    @15
    @43
    cR
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    @15
    @0
    @1
    @4
    @2
    @7
    @43
    @45
    wi
    @24
    @29
    @26
    @31
    @3
    @6
    @7
    @10
    @13
    simp31
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    3noncol.l
    3noncol.j
    3noncol.a
    hlatexch1
    syl131anc
    @15
    @8
    @44
    cR
    c.le
    @15
    @19
    @22
    @23
    @8
    @44
    wceq
    @25
    @30
    @32
    @20
    c.or
    cK
    cP
    cQ
    @27
    3noncol.j
    latjcom
    syl3anc
    breq2d
    sylibrd
    mtod
    cA
    @20
    cP
    cS
    c.or
    cK
    c.le
    @16
    @27
    3noncol.l
    3noncol.j
    3noncol.a
    hlexch1
    syl131anc
    @15
    @41
    @11
    cS
    c.le
    @15
    @41
    cR
    cQ
    c.or
    co
    #
    cP
    c.or
    co
    #
    @11
    @15
    @16
    @46
    cP
    c.or
    @15
    @19
    @23
    @21
    @16
    @46
    wceq
    @25
    @32
    @28
    @20
    c.or
    cK
    cQ
    cR
    @27
    3noncol.j
    latjcom
    syl3anc
    oveq1d
    @15
    @19
    @21
    @23
    @22
    @47
    @11
    wceq
    @25
    @28
    @32
    @30
    @20
    c.or
    cK
    cR
    cQ
    cP
    @27
    3noncol.j
    latj31
    syl13anc
    eqtrd
    breq2d
    sylibd
    mtod
    3jca
end
