include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "w3o.mm"
include "wa.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "jca.mm"
include "simp13.mm"
include "simp23.mm"
include "simp3.mm"
include "4atlem3a.mm"
include "syl31anc.mm"
include "3orass.mm"
include "sylib.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "atbase.mm"
include "latlej2.mm"
include "wceq.mm"
include "hlatj32.mm"
include "syl13anc.mm"
include "breqtrd.mm"
include "biortn.mm"
include "mpbird.mm"

theorem 4atlem3b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ V e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( -. R .<_ ( ( P .\/ Q ) .\/ V ) \/ -. S .<_ ( ( P .\/ Q ) .\/ V ) ) )

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
    cV
    cA
    wcel
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
    @8
    cR
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    w3a
    #
    cR
    @8
    cV
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    @11
    c.le
    wbr
    wn
    #
    wo
    #
    cQ
    @11
    c.le
    wbr
    #
    wn
    #
    @14
    wo
    #
    @10
    @16
    @12
    @13
    w3o
    #
    @17
    @10
    @3
    @4
    @5
    wa
    @2
    @6
    wa
    @9
    @18
    @3
    @7
    @9
    simp1
    @10
    @4
    @5
    @3
    @4
    @5
    @6
    @9
    simp21
    @3
    @4
    @5
    @6
    @9
    simp22
    jca
    @10
    @2
    @6
    @0
    @1
    @2
    @7
    @9
    simp13
    #
    @3
    @4
    @5
    @6
    @9
    simp23
    #
    jca
    @3
    @7
    @9
    simp3
    cA
    cP
    cQ
    cR
    cS
    cQ
    c.or
    cK
    c.le
    cV
    4at.l
    4at.j
    4at.a
    4atlem3a
    syl31anc
    @16
    @12
    @13
    3orass
    sylib
    @10
    @15
    @14
    @17
    wb
    @10
    cQ
    cP
    cV
    c.or
    co
    #
    cQ
    c.or
    co
    #
    @11
    c.le
    @10
    cK
    clat
    wcel
    #
    @21
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @24
    wcel
    #
    cQ
    @22
    c.le
    wbr
    @10
    @0
    @23
    @0
    @1
    @2
    @7
    @9
    simp11
    #
    cK
    hllat
    syl
    @10
    @0
    @1
    @6
    @25
    @27
    @0
    @1
    @2
    @7
    @9
    simp12
    #
    @20
    cA
    @24
    c.or
    cK
    cP
    cV
    @24
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @10
    @2
    @26
    @19
    cA
    @24
    cQ
    cK
    @29
    4at.a
    atbase
    syl
    @24
    c.or
    cK
    c.le
    @21
    cQ
    @29
    4at.l
    4at.j
    latlej2
    syl3anc
    @10
    @0
    @1
    @6
    @2
    @22
    @11
    wceq
    @27
    @28
    @20
    @19
    cA
    cP
    cV
    cQ
    c.or
    cK
    4at.j
    4at.a
    hlatj32
    syl13anc
    breqtrd
    @15
    @14
    biortn
    syl
    mpbird
end
