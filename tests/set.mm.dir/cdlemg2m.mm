include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cdlemg2k.mm"
include "oveq1d.mm"
include "cp0.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2l.mm"
include "eqid.mm"
include "ltrnmw.mm"
include "syl3anc.mm"
include "cbs.mm"
include "simp1l.mm"
include "ltrnel.mm"
include "simpld.mm"
include "simp1r.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "cdleme0aa.mm"
include "syl211anc.mm"
include "lhpbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "hlatjcl.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"

theorem cdlemg2m
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cX: class X
  assume cdlemg2inv.h: |- H = ( LHyp ` K )
  assume cdlemg2inv.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2j.l: |- .<_ = ( le ` K )
  assume cdlemg2j.j: |- .\/ = ( join ` K )
  assume cdlemg2j.a: |- A = ( Atoms ` K )
  assume cdlemg2j.m: |- ./\ = ( meet ` K )
  assume cdlemg2j.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( ( ( F ` P ) .\/ ( F ` Q ) ) ./\ W ) = U )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    c.or
    co
    #
    cW
    c.an
    co
    @12
    cU
    c.or
    co
    #
    cW
    c.an
    co
    #
    cU
    @11
    @13
    @14
    cW
    c.an
    cA
    cP
    cQ
    cT
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg2inv.h
    cdlemg2inv.t
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.a
    cdlemg2j.m
    cdlemg2j.u
    cdlemg2k
    oveq1d
    @11
    @12
    cW
    c.an
    co
    #
    cU
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    cU
    c.or
    co
    #
    @15
    cU
    @11
    @16
    @18
    cU
    c.or
    @11
    @2
    @10
    @5
    @16
    @18
    wceq
    @2
    @9
    @10
    simp1
    #
    @2
    @9
    @10
    simp3
    #
    @2
    @5
    @8
    @10
    simp2l
    #
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    c.an
    cW
    @18
    cdlemg2j.l
    cdlemg2j.m
    @18
    eqid
    #
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnmw
    syl3anc
    oveq1d
    @11
    @0
    @12
    cA
    wcel
    #
    cU
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @25
    wcel
    #
    cU
    cW
    c.le
    wbr
    @17
    @15
    wceq
    @0
    @1
    @9
    @10
    simp1l
    #
    @11
    @24
    @12
    cW
    c.le
    wbr
    wn
    #
    @11
    @2
    @10
    @5
    @24
    @29
    wa
    @20
    @21
    @22
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg2j.l
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnel
    syl3anc
    simpld
    @11
    @0
    @1
    @3
    @6
    @26
    @28
    @0
    @1
    @9
    @10
    simp1r
    #
    @3
    @4
    @8
    @2
    @10
    simp2ll
    #
    @6
    @7
    @5
    @2
    @10
    simp2rl
    #
    cA
    @25
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.m
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2j.u
    @25
    eqid
    #
    cdleme0aa
    syl211anc
    #
    @11
    @1
    @27
    @30
    @25
    cH
    cK
    cW
    @33
    cdlemg2inv.h
    lhpbase
    syl
    #
    @11
    cU
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdlemg2j.u
    @11
    cK
    clat
    wcel
    #
    @36
    @25
    wcel
    #
    @27
    @37
    cW
    c.le
    wbr
    @11
    @0
    @38
    @28
    cK
    hllat
    syl
    @11
    @0
    @3
    @6
    @39
    @28
    @31
    @32
    cA
    @25
    c.or
    cK
    cP
    cQ
    @33
    cdlemg2j.j
    cdlemg2j.a
    hlatjcl
    syl3anc
    @35
    @25
    cK
    c.le
    c.an
    @36
    cW
    @33
    cdlemg2j.l
    cdlemg2j.m
    latmle2
    syl3anc
    syl5eqbr
    cA
    @25
    @12
    c.or
    cK
    c.le
    c.an
    cU
    cW
    @33
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.m
    cdlemg2j.a
    atmod4i2
    syl131anc
    @11
    cK
    col
    wcel
    #
    @26
    @19
    cU
    wceq
    @11
    @0
    @40
    @28
    cK
    hlol
    syl
    @34
    @25
    c.or
    cK
    cU
    @18
    @33
    cdlemg2j.j
    @23
    olj02
    syl2anc
    3eqtr3d
    eqtrd
end
