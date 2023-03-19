include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "simp22.mm"
include "simp31l.mm"
include "simp31r.mm"
include "simp32.mm"
include "cdlemg35.mm"
include "syl133anc.mm"
include "simp2.mm"
include "simp3l.mm"
include "jca.mm"
include "simp121.mm"
include "simp122.mm"
include "simp123.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "simp133.mm"
include "eqid.mm"
include "cdlemg34.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemg36
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
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  let vv: setvar v
  assume cdlemg35.l: |- .<_ = ( le ` K )
  assume cdlemg35.j: |- .\/ = ( join ` K )
  assume cdlemg35.m: |- ./\ = ( meet ` K )
  assume cdlemg35.a: |- A = ( Atoms ` K )
  assume cdlemg35.h: |- H = ( LHyp ` K )
  assume cdlemg35.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg35.r: |- R = ( ( trL ` K ) ` W )

  disjoint A r
  disjoint F r
  disjoint G r
  disjoint H r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint ./\ r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint W r
  disjoint A v
  disjoint F v
  disjoint G v
  disjoint H v
  disjoint K v
  disjoint .<_ v
  disjoint P v
  disjoint R v
  disjoint T v
  disjoint W v
  disjoint r v
  disjoint .\/ v
  disjoint ./\ v
  disjoint Q v
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( ( F ` P ) =/= P /\ ( G ` P ) =/= P ) /\ ( R ` F ) =/= ( R ` G ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    w3a
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cF
    cfv
    cP
    wne
    #
    cP
    cG
    cfv
    #
    cP
    wne
    #
    wa
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @15
    c.or
    co
    cQ
    @15
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    cv
    #
    cW
    c.le
    wbr
    #
    @19
    @12
    wne
    #
    @19
    @13
    wne
    #
    wa
    #
    wa
    #
    vv
    cA
    wrex
    #
    cP
    @9
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    cQ
    cQ
    cG
    cfv
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    wceq
    #
    @18
    @0
    @1
    @4
    @5
    @8
    @10
    @14
    @25
    @0
    @1
    @2
    @7
    @17
    simp11
    @0
    @1
    @2
    @7
    @17
    simp12
    @3
    @4
    @5
    @6
    @17
    simp21
    @3
    @4
    @5
    @6
    @17
    simp22
    @8
    @10
    @14
    @16
    @3
    @7
    simp31l
    @8
    @10
    @14
    @16
    @3
    @7
    simp31r
    @3
    @7
    @11
    @14
    @16
    simp32
    vv
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg35
    syl133anc
    @18
    @24
    @26
    vv
    cA
    @18
    @19
    cA
    wcel
    #
    @24
    w3a
    #
    @3
    @27
    @20
    wa
    @4
    @5
    wa
    @6
    @21
    @22
    @16
    @26
    @3
    @7
    @17
    @27
    @24
    simp11
    @28
    @27
    @20
    @18
    @27
    @24
    simp2
    @18
    @27
    @20
    @23
    simp3l
    jca
    @28
    @4
    @5
    @4
    @5
    @6
    @3
    @17
    @27
    @24
    simp121
    @4
    @5
    @6
    @3
    @17
    @27
    @24
    simp122
    jca
    @4
    @5
    @6
    @3
    @17
    @27
    @24
    simp123
    @21
    @22
    @20
    @18
    @27
    simp3rl
    @21
    @22
    @20
    @18
    @27
    simp3rr
    @11
    @14
    @16
    @3
    @7
    @27
    @24
    simp133
    vv
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
    c.an
    cP
    @19
    c.or
    co
    #
    cQ
    @12
    c.or
    co
    c.an
    co
    #
    @29
    cQ
    @13
    c.or
    co
    c.an
    co
    #
    cW
    vr
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    @30
    eqid
    @31
    eqid
    cdlemg34
    syl133anc
    rexlimdv3a
    mpd
end
