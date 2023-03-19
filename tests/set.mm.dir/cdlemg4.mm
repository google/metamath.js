include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cmee.mm"
include "eqid.mm"
include "cdlemg4g.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "cbs.mm"
include "simp1.mm"
include "simp31.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "simp32.mm"
include "wi.mm"
include "simp21r.mm"
include "simp21.mm"
include "trlval2.mm"
include "syl5eq.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "ltrnel.mm"
include "simpld.mm"
include "hlatjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "eqbrtrd.mm"
include "atbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "mtod.mm"
include "hlexch2.mm"
include "syl131anc.mm"
include "2llnma1b.mm"
include "3eqtrd.mm"

theorem cdlemg4
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
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( F ` ( G ` Q ) ) = Q )

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
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
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
    cF
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
    #
    cQ
    cP
    cV
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    cV
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    cK
    cmee
    cfv
    #
    co
    @19
    cQ
    cP
    c.or
    co
    #
    @21
    co
    #
    cQ
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
    @21
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    @21
    eqid
    #
    cdlemg4g
    @18
    @20
    @22
    @19
    @21
    @18
    @0
    @3
    @7
    @20
    @22
    wceq
    @0
    @1
    @11
    @17
    simp1l
    #
    @3
    @5
    @9
    @10
    @2
    @17
    simp21l
    #
    @7
    @8
    @6
    @10
    @2
    @17
    simp22l
    #
    cA
    c.or
    cK
    cP
    cQ
    cdlemg4.j
    cdlemg4.a
    hlatjcom
    syl3anc
    oveq2d
    @18
    @0
    cV
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @3
    cP
    @19
    c.le
    wbr
    #
    wn
    @23
    cQ
    wceq
    @25
    @18
    cV
    cG
    cR
    cfv
    #
    @28
    cdlemg4b.v
    @18
    @2
    @12
    @31
    @28
    wcel
    @2
    @11
    @17
    simp1
    #
    @2
    @11
    @12
    @14
    @16
    simp31
    #
    @28
    cR
    cT
    cG
    cH
    cK
    cW
    @28
    eqid
    #
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlcl
    syl2anc
    syl5eqel
    #
    @27
    @26
    @18
    @30
    @13
    @2
    @11
    @12
    @14
    @16
    simp32
    @18
    @0
    @3
    @7
    @29
    cP
    cV
    c.le
    wbr
    #
    wn
    @30
    @13
    wi
    @25
    @26
    @27
    @35
    @18
    @36
    @4
    @3
    @5
    @9
    @10
    @2
    @17
    simp21r
    @18
    @36
    cV
    cW
    c.le
    wbr
    #
    @4
    @18
    cV
    cP
    @15
    c.or
    co
    #
    cW
    @21
    co
    #
    cW
    c.le
    @18
    cV
    @31
    @39
    cdlemg4b.v
    @18
    @2
    @12
    @6
    @31
    @39
    wceq
    @32
    @33
    @2
    @6
    @9
    @10
    @17
    simp21
    #
    cA
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    @21
    cW
    cdlemg4.l
    cdlemg4.j
    @24
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlval2
    syl3anc
    syl5eq
    @18
    cK
    clat
    wcel
    #
    @38
    @28
    wcel
    #
    cW
    @28
    wcel
    #
    @39
    cW
    c.le
    wbr
    @18
    @0
    @41
    @25
    cK
    hllat
    syl
    #
    @18
    @0
    @3
    @15
    cA
    wcel
    #
    @42
    @25
    @26
    @18
    @45
    @15
    cW
    c.le
    wbr
    wn
    #
    @18
    @2
    @12
    @6
    @45
    @46
    wa
    @32
    @33
    @40
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    ltrnel
    syl3anc
    simpld
    cA
    @28
    c.or
    cK
    cP
    @15
    @34
    cdlemg4.j
    cdlemg4.a
    hlatjcl
    syl3anc
    @18
    @1
    @43
    @0
    @1
    @11
    @17
    simp1r
    @28
    cH
    cK
    cW
    @34
    cdlemg4.h
    lhpbase
    syl
    #
    @28
    cK
    c.le
    @21
    @38
    cW
    @34
    cdlemg4.l
    @24
    latmle2
    syl3anc
    eqbrtrd
    @18
    @41
    cP
    @28
    wcel
    #
    @29
    @43
    @36
    @37
    wa
    @4
    wi
    @44
    @18
    @3
    @48
    @26
    cA
    @28
    cP
    cK
    @34
    cdlemg4.a
    atbase
    syl
    @35
    @47
    @28
    cK
    c.le
    cP
    cV
    cW
    @34
    cdlemg4.l
    lattr
    syl13anc
    mpan2d
    mtod
    cA
    @28
    cP
    cQ
    c.or
    cK
    c.le
    cV
    @34
    cdlemg4.l
    cdlemg4.j
    cdlemg4.a
    hlexch2
    syl131anc
    mtod
    cA
    @28
    cQ
    cP
    c.or
    cK
    c.le
    @21
    cV
    @34
    cdlemg4.l
    cdlemg4.j
    @24
    cdlemg4.a
    2llnma1b
    syl131anc
    3eqtrd
end
