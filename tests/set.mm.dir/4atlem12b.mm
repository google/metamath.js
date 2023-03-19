include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "simp11.mm"
include "simp121.mm"
include "simp122.mm"
include "jca.mm"
include "simp13.mm"
include "3jca.mm"
include "simp2l.mm"
include "simp3lr.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp111.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp123.mm"
include "simp131.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp132.mm"
include "simp133.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp113.mm"
include "simp3ll.mm"
include "simp112.mm"
include "simp2r.mm"
include "4atlem12a.mm"
include "syl311anc.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "4atlem11.mm"
include "sylc.mm"
include "eqtrd.mm"

theorem 4atlem12b
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
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( U e. A /\ V e. A /\ W e. A ) ) /\ ( ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) /\ -. P .<_ ( ( U .\/ V ) .\/ W ) ) /\ ( ( P .<_ ( ( T .\/ U ) .\/ ( V .\/ W ) ) /\ Q .<_ ( ( T .\/ U ) .\/ ( V .\/ W ) ) ) /\ ( R .<_ ( ( T .\/ U ) .\/ ( V .\/ W ) ) /\ S .<_ ( ( T .\/ U ) .\/ ( V .\/ W ) ) ) ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( T .\/ U ) .\/ ( V .\/ W ) ) )

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
    @13
    cR
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    cP
    cU
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
    cP
    cT
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
    cQ
    @19
    c.le
    wbr
    #
    wa
    #
    cR
    @19
    c.le
    wbr
    #
    cS
    @19
    c.le
    wbr
    #
    wa
    #
    wa
    #
    w3a
    #
    @13
    cR
    cS
    c.or
    co
    #
    c.or
    co
    #
    cP
    cU
    c.or
    co
    @18
    c.or
    co
    #
    @19
    @27
    @3
    @4
    @5
    wa
    #
    @11
    w3a
    #
    @14
    wa
    cQ
    @28
    c.or
    co
    #
    @30
    c.le
    wbr
    @29
    @30
    wceq
    @27
    @32
    @14
    @27
    @3
    @31
    @11
    @3
    @7
    @11
    @16
    @26
    simp11
    @27
    @4
    @5
    @4
    @5
    @6
    @3
    @11
    @16
    @26
    simp121
    #
    @4
    @5
    @6
    @3
    @11
    @16
    @26
    simp122
    #
    jca
    @3
    @7
    @11
    @16
    @26
    simp13
    #
    3jca
    @12
    @14
    @15
    @26
    simp2l
    jca
    @27
    @33
    @19
    @30
    c.le
    @27
    @21
    @28
    @19
    c.le
    wbr
    #
    @33
    @19
    c.le
    wbr
    #
    @20
    @21
    @25
    @12
    @16
    simp3lr
    @27
    @23
    @24
    @37
    @23
    @24
    @22
    @12
    @16
    simp3rl
    @23
    @24
    @22
    @12
    @16
    simp3rr
    @27
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
    @40
    wcel
    #
    @19
    @40
    wcel
    #
    @25
    @37
    wb
    @27
    @0
    @39
    @0
    @1
    @2
    @7
    @11
    @16
    @26
    simp111
    #
    cK
    hllat
    syl
    #
    @27
    @4
    @41
    @34
    cA
    @40
    cR
    cK
    @40
    eqid
    #
    4at.a
    atbase
    syl
    @27
    @5
    @42
    @35
    cA
    @40
    cS
    cK
    @46
    4at.a
    atbase
    syl
    @27
    @39
    @17
    @40
    wcel
    #
    @18
    @40
    wcel
    #
    @43
    @45
    @27
    @0
    @6
    @8
    @47
    @44
    @4
    @5
    @6
    @3
    @11
    @16
    @26
    simp123
    #
    @8
    @9
    @10
    @3
    @7
    @16
    @26
    simp131
    cA
    @40
    c.or
    cK
    cT
    cU
    @46
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @27
    @0
    @9
    @10
    @48
    @44
    @8
    @9
    @10
    @3
    @7
    @16
    @26
    simp132
    @8
    @9
    @10
    @3
    @7
    @16
    @26
    simp133
    cA
    @40
    c.or
    cK
    cV
    cW
    @46
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @40
    c.or
    cK
    @17
    @18
    @46
    4at.j
    latjcl
    syl3anc
    #
    @40
    c.or
    cK
    c.le
    cR
    cS
    @19
    @46
    4at.l
    4at.j
    latjle12
    syl13anc
    mpbi2and
    @27
    @39
    cQ
    @40
    wcel
    #
    @28
    @40
    wcel
    #
    @43
    @21
    @37
    wa
    @38
    wb
    @45
    @27
    @2
    @51
    @0
    @1
    @2
    @7
    @11
    @16
    @26
    simp113
    cA
    @40
    cQ
    cK
    @46
    4at.a
    atbase
    syl
    @27
    @0
    @4
    @5
    @52
    @44
    @34
    @35
    cA
    @40
    c.or
    cK
    cR
    cS
    @46
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @50
    @40
    c.or
    cK
    c.le
    cQ
    @28
    @19
    @46
    4at.l
    4at.j
    latjle12
    syl13anc
    mpbi2and
    @27
    @20
    @30
    @19
    wceq
    #
    @20
    @21
    @25
    @12
    @16
    simp3ll
    @27
    @0
    @1
    @6
    @11
    @15
    @20
    @53
    wb
    @44
    @0
    @1
    @2
    @7
    @11
    @16
    @26
    simp112
    @49
    @36
    @12
    @14
    @15
    @26
    simp2r
    cA
    cP
    cT
    cU
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem12a
    syl311anc
    mpbid
    #
    breqtrrd
    cA
    cP
    cQ
    cR
    cS
    cU
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem11
    sylc
    @54
    eqtrd
end
