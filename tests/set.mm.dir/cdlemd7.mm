include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wne.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "clat.mm"
include "cbs.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2rl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp2ll.mm"
include "simp11.mm"
include "simp12l.mm"
include "ltrncl.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "latnlej1l.mm"
include "necomd.mm"
include "syl131anc.mm"
include "simp3l.mm"
include "simp12.mm"
include "cdlemd6.mm"
include "syl231anc.mm"
include "cdlemd5.mm"
include "syl132anc.mm"

theorem cdlemd7
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vs: setvar s
  assume cdlemd4.l: |- .<_ = ( le ` K )
  assume cdlemd4.j: |- .\/ = ( join ` K )
  assume cdlemd4.a: |- A = ( Atoms ` K )
  assume cdlemd4.h: |- H = ( LHyp ` K )
  assume cdlemd4.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ R e. A ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F ` P ) = ( G ` P ) /\ -. Q .<_ ( P .\/ ( F ` P ) ) ) ) -> ( F ` R ) = ( G ` R ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cP
    cF
    cfv
    #
    cP
    cG
    cfv
    wceq
    #
    cQ
    cP
    @15
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @7
    @10
    @13
    cP
    cQ
    wne
    #
    @16
    cQ
    cF
    cfv
    cQ
    cG
    cfv
    wceq
    #
    cR
    cF
    cfv
    cR
    cG
    cfv
    wceq
    @7
    @14
    @18
    simp1
    @7
    @10
    @13
    @18
    simp2l
    #
    @7
    @10
    @13
    @18
    simp2r
    #
    @19
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @25
    wcel
    #
    @15
    @25
    wcel
    #
    @17
    @20
    @19
    @0
    @24
    @0
    @1
    @5
    @6
    @14
    @18
    simp11l
    cK
    hllat
    syl
    @19
    @11
    @26
    @11
    @12
    @10
    @7
    @18
    simp2rl
    cA
    @25
    cQ
    cK
    @25
    eqid
    #
    cdlemd4.a
    atbase
    syl
    @19
    @8
    @27
    @8
    @9
    @13
    @7
    @18
    simp2ll
    cA
    @25
    cP
    cK
    @29
    cdlemd4.a
    atbase
    syl
    #
    @19
    @2
    @3
    @27
    @28
    @2
    @5
    @6
    @14
    @18
    simp11
    #
    @3
    @4
    @2
    @6
    @14
    @18
    simp12l
    @30
    @25
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    @29
    cdlemd4.h
    cdlemd4.t
    ltrncl
    syl3anc
    @7
    @14
    @16
    @17
    simp3r
    #
    @24
    @26
    @27
    @28
    w3a
    @17
    w3a
    cQ
    cP
    @25
    c.or
    cK
    c.le
    cQ
    cP
    @15
    @29
    cdlemd4.l
    cdlemd4.j
    latnlej1l
    necomd
    syl131anc
    @7
    @14
    @16
    @17
    simp3l
    #
    @19
    @2
    @5
    @10
    @13
    @17
    @16
    @21
    @31
    @2
    @5
    @6
    @14
    @18
    simp12
    @22
    @23
    @32
    @33
    cA
    cP
    cQ
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    cdlemd6
    syl231anc
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    cdlemd5
    syl132anc
end
