include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp132.mm"
include "simp133.mm"
include "3jca.mm"
include "simp2l.mm"
include "simp32.mm"
include "simp33.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp111.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp12r.mm"
include "simp112.mm"
include "simp131.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp31.mm"
include "simp13.mm"
include "simp2r.mm"
include "4atlem11a.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "4atlem10.mm"
include "sylc.mm"
include "eqtrd.mm"

theorem 4atlem11b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( U e. A /\ V e. A /\ W e. A ) ) /\ ( ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) /\ -. Q .<_ ( ( P .\/ V ) .\/ W ) ) /\ ( Q .<_ ( ( P .\/ U ) .\/ ( V .\/ W ) ) /\ R .<_ ( ( P .\/ U ) .\/ ( V .\/ W ) ) /\ S .<_ ( ( P .\/ U ) .\/ ( V .\/ W ) ) ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( P .\/ U ) .\/ ( V .\/ W ) ) )

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
    cU
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    cW
    cA
    wcel
    #
    w3a
    #
    w3a
    #
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cS
    @12
    cR
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    cQ
    cP
    cV
    c.or
    co
    cW
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cP
    cU
    c.or
    co
    #
    cV
    cW
    c.or
    co
    #
    c.or
    co
    #
    c.le
    wbr
    #
    cR
    @18
    c.le
    wbr
    #
    cS
    @18
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    @12
    cR
    cS
    c.or
    co
    #
    c.or
    co
    #
    @12
    @17
    c.or
    co
    #
    @18
    @23
    @3
    @6
    @8
    @9
    w3a
    #
    @13
    w3a
    @24
    @26
    c.le
    wbr
    @25
    @26
    wceq
    @23
    @3
    @27
    @13
    @3
    @6
    @10
    @15
    @22
    simp11
    #
    @23
    @6
    @8
    @9
    @3
    @6
    @10
    @15
    @22
    simp12
    @7
    @8
    @9
    @3
    @6
    @15
    @22
    simp132
    #
    @7
    @8
    @9
    @3
    @6
    @15
    @22
    simp133
    #
    3jca
    @11
    @13
    @14
    @22
    simp2l
    3jca
    @23
    @24
    @18
    @26
    c.le
    @23
    @20
    @21
    @24
    @18
    c.le
    wbr
    #
    @11
    @15
    @19
    @20
    @21
    simp32
    @11
    @15
    @19
    @20
    @21
    simp33
    @23
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
    cS
    @33
    wcel
    #
    @18
    @33
    wcel
    #
    @20
    @21
    wa
    @31
    wb
    @23
    @0
    @32
    @0
    @1
    @2
    @6
    @10
    @15
    @22
    simp111
    #
    cK
    hllat
    syl
    #
    @23
    @4
    @34
    @4
    @5
    @3
    @10
    @15
    @22
    simp12l
    cA
    @33
    cR
    cK
    @33
    eqid
    #
    4at.a
    atbase
    syl
    @23
    @5
    @35
    @4
    @5
    @3
    @10
    @15
    @22
    simp12r
    cA
    @33
    cS
    cK
    @39
    4at.a
    atbase
    syl
    @23
    @32
    @16
    @33
    wcel
    #
    @17
    @33
    wcel
    #
    @36
    @38
    @23
    @0
    @1
    @7
    @40
    @37
    @0
    @1
    @2
    @6
    @10
    @15
    @22
    simp112
    @7
    @8
    @9
    @3
    @6
    @15
    @22
    simp131
    cA
    @33
    c.or
    cK
    cP
    cU
    @39
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @23
    @0
    @8
    @9
    @41
    @37
    @29
    @30
    cA
    @33
    c.or
    cK
    cV
    cW
    @39
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @33
    c.or
    cK
    @16
    @17
    @39
    4at.j
    latjcl
    syl3anc
    @33
    c.or
    cK
    c.le
    cR
    cS
    @18
    @39
    4at.l
    4at.j
    latjle12
    syl13anc
    mpbi2and
    @23
    @19
    @26
    @18
    wceq
    #
    @11
    @15
    @19
    @20
    @21
    simp31
    @23
    @3
    @10
    @14
    @19
    @42
    wb
    @28
    @3
    @6
    @10
    @15
    @22
    simp13
    @11
    @13
    @14
    @22
    simp2r
    cA
    cP
    cQ
    cU
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem11a
    syl3anc
    mpbid
    #
    breqtrrd
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem10
    sylc
    @43
    eqtrd
end
