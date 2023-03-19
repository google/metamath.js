include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "ctrl.mm"
include "cmee.mm"
include "simp3.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "simp1l.mm"
include "simp1rl.mm"
include "simp21.mm"
include "eqid.mm"
include "trlval2.mm"
include "syl3anc.mm"
include "simp1rr.mm"
include "3eqtr4d.mm"
include "oveq12d.mm"
include "simp22.mm"
include "simp23.mm"
include "cdlemc.mm"
include "syl131anc.mm"
include "oveq2.mm"
include "breq2d.mm"
include "notbid.mm"
include "biimpd.mm"
include "sylc.mm"

theorem cdlemd6
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vs: setvar s
  let cR: class R
  assume cdlemd4.l: |- .<_ = ( le ` K )
  assume cdlemd4.j: |- .\/ = ( join ` K )
  assume cdlemd4.a: |- A = ( Atoms ` K )
  assume cdlemd4.h: |- H = ( LHyp ` K )
  assume cdlemd4.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ -. Q .<_ ( P .\/ ( F ` P ) ) ) /\ ( F ` P ) = ( G ` P ) ) -> ( F ` Q ) = ( G ` Q ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cP
    cP
    cF
    cfv
    #
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
    @7
    cP
    cG
    cfv
    #
    wceq
    #
    w3a
    #
    cQ
    cF
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    c.or
    co
    #
    @7
    cP
    cQ
    c.or
    co
    cW
    cK
    cmee
    cfv
    #
    co
    #
    c.or
    co
    #
    @18
    co
    #
    cQ
    cG
    @15
    cfv
    #
    c.or
    co
    #
    @12
    @19
    c.or
    co
    #
    @18
    co
    #
    cQ
    cF
    cfv
    #
    cQ
    cG
    cfv
    #
    @14
    @17
    @23
    @20
    @24
    @18
    @14
    @16
    @22
    cQ
    c.or
    @14
    @8
    cW
    @18
    co
    #
    cP
    @12
    c.or
    co
    #
    cW
    @18
    co
    #
    @16
    @22
    @14
    @8
    @29
    cW
    @18
    @14
    @7
    @12
    cP
    c.or
    @4
    @11
    @13
    simp3
    #
    oveq2d
    oveq1d
    @14
    @0
    @1
    @5
    @16
    @28
    wceq
    @0
    @3
    @11
    @13
    simp1l
    #
    @1
    @2
    @0
    @11
    @13
    simp1rl
    #
    @4
    @5
    @6
    @10
    @13
    simp21
    #
    cA
    cP
    @15
    cT
    cF
    cH
    c.or
    cK
    c.le
    @18
    cW
    cdlemd4.l
    cdlemd4.j
    @18
    eqid
    #
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    @15
    eqid
    #
    trlval2
    syl3anc
    @14
    @0
    @2
    @5
    @22
    @30
    wceq
    @32
    @1
    @2
    @0
    @11
    @13
    simp1rr
    #
    @34
    cA
    cP
    @15
    cT
    cG
    cH
    c.or
    cK
    c.le
    @18
    cW
    cdlemd4.l
    cdlemd4.j
    @35
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    @36
    trlval2
    syl3anc
    3eqtr4d
    oveq2d
    @14
    @7
    @12
    @19
    c.or
    @31
    oveq1d
    oveq12d
    @14
    @0
    @1
    @5
    @6
    @10
    @26
    @21
    wceq
    @32
    @33
    @34
    @4
    @5
    @6
    @10
    @13
    simp22
    #
    @4
    @5
    @6
    @10
    @13
    simp23
    #
    cA
    cP
    cQ
    @15
    cT
    cF
    cH
    c.or
    cK
    c.le
    @18
    cW
    cdlemd4.l
    cdlemd4.j
    @35
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    @36
    cdlemc
    syl131anc
    @14
    @0
    @2
    @5
    @6
    cQ
    @29
    c.le
    wbr
    #
    wn
    #
    @27
    @25
    wceq
    @32
    @37
    @34
    @38
    @14
    @13
    @10
    @41
    @31
    @39
    @13
    @10
    @41
    @13
    @9
    @40
    @13
    @8
    @29
    cQ
    c.le
    @7
    @12
    cP
    c.or
    oveq2
    breq2d
    notbid
    biimpd
    sylc
    cA
    cP
    cQ
    @15
    cT
    cG
    cH
    c.or
    cK
    c.le
    @18
    cW
    cdlemd4.l
    cdlemd4.j
    @35
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    @36
    cdlemc
    syl131anc
    3eqtr4d
end
