include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp21.mm"
include "simp22.mm"
include "simp231.mm"
include "cdlemb2.mm"
include "syl221anc.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simprl.mm"
include "simprrl.mm"
include "jca.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simprrr.mm"
include "latnlej1l.mm"
include "necomd.mm"
include "syl131anc.mm"
include "simpl22.mm"
include "simpl23.mm"
include "cdlemd3.mm"
include "syl133anc.mm"
include "simpl3l.mm"
include "simpl3.mm"
include "cdlemd2.mm"
include "syl331anc.mm"
include "syl332anc.mm"
include "rexlimddv.mm"

theorem cdlemd4
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ R e. A ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ R =/= P ) ) /\ ( ( F ` P ) = ( G ` P ) /\ ( F ` Q ) = ( G ` Q ) ) ) -> ( F ` R ) = ( G ` R ) )

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
    cG
    cT
    wcel
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
    cR
    cP
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cF
    cfv
    cP
    cG
    cfv
    wceq
    #
    cQ
    cF
    cfv
    cQ
    cG
    cfv
    wceq
    #
    wa
    #
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @22
    @13
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    cF
    cfv
    cR
    cG
    cfv
    wceq
    #
    vs
    cA
    @21
    @0
    @1
    @8
    @11
    @12
    @25
    vs
    cA
    wrex
    @0
    @1
    @3
    @4
    @17
    @20
    simp11l
    #
    @0
    @1
    @3
    @4
    @17
    @20
    simp11r
    @5
    @8
    @11
    @16
    @20
    simp21
    @5
    @8
    @11
    @16
    @20
    simp22
    @12
    @14
    @15
    @8
    @11
    @5
    @20
    simp231
    #
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vs
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemb2
    syl221anc
    @21
    @22
    cA
    wcel
    #
    @25
    wa
    #
    wa
    #
    @2
    @3
    @4
    @8
    @29
    @23
    wa
    cP
    @22
    wne
    #
    cR
    cP
    @22
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    @18
    @22
    cF
    cfv
    @22
    cG
    cfv
    wceq
    #
    @26
    @2
    @3
    @4
    @17
    @20
    @30
    simpl11
    #
    @2
    @3
    @4
    @17
    @20
    @30
    simpl12
    #
    @2
    @3
    @4
    @17
    @20
    @30
    simpl13
    #
    @8
    @11
    @16
    @5
    @20
    @30
    simpl21
    #
    @31
    @29
    @23
    @21
    @29
    @25
    simprl
    #
    @21
    @29
    @23
    @24
    simprrl
    jca
    @31
    @32
    @33
    @31
    cK
    clat
    wcel
    #
    @22
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @41
    wcel
    #
    cQ
    @41
    wcel
    #
    @24
    @32
    @21
    @40
    @30
    @21
    @0
    @40
    @27
    cK
    hllat
    syl
    adantr
    @29
    @42
    @21
    @25
    cA
    @41
    @22
    cK
    @41
    eqid
    #
    cdlemd4.a
    atbase
    ad2antrl
    @21
    @43
    @30
    @21
    @6
    @43
    @6
    @7
    @11
    @16
    @5
    @20
    simp21l
    cA
    @41
    cP
    cK
    @45
    cdlemd4.a
    atbase
    syl
    adantr
    @21
    @44
    @30
    @21
    @9
    @44
    @9
    @10
    @8
    @16
    @5
    @20
    simp22l
    cA
    @41
    cQ
    cK
    @45
    cdlemd4.a
    atbase
    syl
    adantr
    @21
    @29
    @23
    @24
    simprrr
    #
    @40
    @42
    @43
    @44
    w3a
    @24
    w3a
    @22
    cP
    @41
    c.or
    cK
    c.le
    @22
    cP
    cQ
    @45
    cdlemd4.l
    cdlemd4.j
    latnlej1l
    necomd
    syl131anc
    @31
    @2
    @8
    @11
    @16
    @4
    @29
    @24
    @33
    @35
    @38
    @8
    @11
    @16
    @5
    @20
    @30
    simpl22
    #
    @8
    @11
    @16
    @5
    @20
    @30
    simpl23
    @37
    @39
    @46
    cA
    cP
    cQ
    cR
    @22
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd3
    syl133anc
    jca
    @18
    @19
    @5
    @17
    @30
    simpl3l
    @31
    @2
    @3
    @29
    @8
    @11
    @12
    @24
    wa
    @20
    @34
    @35
    @36
    @39
    @38
    @47
    @31
    @12
    @24
    @21
    @12
    @30
    @28
    adantr
    @46
    jca
    @5
    @17
    @20
    @30
    simpl3
    cA
    cP
    cQ
    @22
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
    cdlemd2
    syl331anc
    cA
    cP
    @22
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
    cdlemd2
    syl332anc
    rexlimddv
end
