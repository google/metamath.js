include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp21r.mm"
include "hlatjcl.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "simp23.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "wi.mm"
include "3jca.mm"
include "simp2.mm"
include "simp33.mm"
include "simp3.mm"
include "4atlem10b.mm"
include "syl31anc.mm"
include "3exp.mm"
include "hlatjcom.mm"
include "oveq2d.mm"
include "simp12.mm"
include "simp13.mm"
include "jca.mm"
include "simp21.mm"
include "simp32.mm"
include "4atlem0a.mm"
include "syl32anc.mm"
include "simprr.mm"
include "simprl.mm"
include "3adant2.mm"
include "eqtr3d.mm"
include "wo.mm"
include "simp1.mm"
include "4atlem3b.mm"
include "syl131anc.mm"
include "mpjaod.mm"
include "sylbird.mm"

theorem 4atlem10
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( ( R e. A /\ S e. A ) /\ V e. A /\ W e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( ( R .\/ S ) .<_ ( ( P .\/ Q ) .\/ ( V .\/ W ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( P .\/ Q ) .\/ ( V .\/ W ) ) ) )

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
    wn
    #
    cS
    @11
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cR
    cS
    c.or
    co
    #
    @11
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
    wa
    #
    @11
    @16
    c.or
    co
    #
    @18
    wceq
    #
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
    cS
    @26
    wcel
    #
    @18
    @26
    wcel
    #
    @22
    @19
    wb
    @15
    @0
    @25
    @0
    @1
    @2
    @9
    @14
    simp11
    #
    cK
    hllat
    syl
    #
    @15
    @4
    @27
    @4
    @5
    @7
    @8
    @3
    @14
    simp21l
    #
    cA
    @26
    cR
    cK
    @26
    eqid
    #
    4at.a
    atbase
    syl
    @15
    @5
    @28
    @4
    @5
    @7
    @8
    @3
    @14
    simp21r
    #
    cA
    @26
    cS
    cK
    @33
    4at.a
    atbase
    syl
    @15
    @25
    @11
    @26
    wcel
    #
    @17
    @26
    wcel
    #
    @29
    @31
    @3
    @9
    @35
    @14
    cA
    @26
    c.or
    cK
    cP
    cQ
    @33
    4at.j
    4at.a
    hlatjcl
    3ad2ant1
    @15
    @0
    @7
    @8
    @36
    @30
    @3
    @6
    @7
    @8
    @14
    simp22
    #
    @3
    @6
    @7
    @8
    @14
    simp23
    #
    cA
    @26
    c.or
    cK
    cV
    cW
    @33
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @26
    c.or
    cK
    @11
    @17
    @33
    4at.j
    latjcl
    syl3anc
    @26
    c.or
    cK
    c.le
    cR
    cS
    @18
    @33
    4at.l
    4at.j
    latjle12
    syl13anc
    @15
    cR
    @11
    cW
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @22
    @24
    wi
    cS
    @39
    c.le
    wbr
    wn
    #
    @15
    @40
    @22
    @24
    @15
    @40
    @22
    w3a
    #
    @3
    @4
    @5
    @7
    w3a
    #
    @8
    @40
    @13
    w3a
    @22
    @24
    @3
    @9
    @14
    @40
    @22
    simp11
    @15
    @40
    @43
    @22
    @15
    @4
    @5
    @7
    @32
    @34
    @37
    3jca
    3ad2ant1
    @42
    @8
    @40
    @13
    @15
    @40
    @8
    @22
    @38
    3ad2ant1
    @15
    @40
    @22
    simp2
    @15
    @40
    @13
    @22
    @3
    @9
    @10
    @12
    @13
    simp33
    #
    3ad2ant1
    3jca
    @15
    @40
    @22
    simp3
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
    4atlem10b
    syl31anc
    3exp
    @15
    @41
    @22
    @24
    @15
    @41
    @22
    w3a
    #
    @11
    cS
    cR
    c.or
    co
    #
    c.or
    co
    #
    @23
    @18
    @15
    @41
    @47
    @23
    wceq
    @22
    @15
    @46
    @16
    @11
    c.or
    @15
    @0
    @5
    @4
    @46
    @16
    wceq
    @30
    @34
    @32
    cA
    c.or
    cK
    cS
    cR
    4at.j
    4at.a
    hlatjcom
    syl3anc
    oveq2d
    3ad2ant1
    @45
    @3
    @5
    @4
    @7
    w3a
    #
    @8
    @41
    cR
    @11
    cS
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    @21
    @20
    wa
    #
    @47
    @18
    wceq
    @3
    @9
    @14
    @41
    @22
    simp11
    @15
    @41
    @48
    @22
    @15
    @5
    @4
    @7
    @34
    @32
    @37
    3jca
    3ad2ant1
    @45
    @8
    @41
    @49
    @15
    @41
    @8
    @22
    @38
    3ad2ant1
    @15
    @41
    @22
    simp2
    @15
    @41
    @49
    @22
    @15
    @0
    @1
    @2
    wa
    @6
    @12
    @13
    @49
    @30
    @15
    @1
    @2
    @0
    @1
    @2
    @9
    @14
    simp12
    @0
    @1
    @2
    @9
    @14
    simp13
    jca
    @3
    @6
    @7
    @8
    @14
    simp21
    @3
    @9
    @10
    @12
    @13
    simp32
    @44
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    4atlem0a
    syl32anc
    3ad2ant1
    3jca
    @15
    @22
    @50
    @41
    @15
    @22
    wa
    @21
    @20
    @15
    @20
    @21
    simprr
    @15
    @20
    @21
    simprl
    jca
    3adant2
    cA
    cP
    cQ
    cS
    cR
    c.or
    cK
    c.le
    cV
    cW
    4at.l
    4at.j
    4at.a
    4atlem10b
    syl31anc
    eqtr3d
    3exp
    @15
    @3
    @4
    @5
    @8
    @14
    @40
    @41
    wo
    @3
    @9
    @14
    simp1
    @32
    @34
    @38
    @3
    @9
    @14
    simp3
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    cW
    4at.l
    4at.j
    4at.a
    4atlem3b
    syl131anc
    mpjaod
    sylbird
end
