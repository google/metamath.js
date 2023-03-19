include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "simp23.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp23l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp1r.mm"
include "simp21l.mm"
include "simp22l.mm"
include "cdleme0aa.mm"
include "syl211anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp23r.mm"
include "latlej1.mm"
include "wi.mm"
include "lhpbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "jca.mm"
include "simp3.mm"
include "cp0.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "hlatjcl.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "cdlemg2fv.mm"
include "syl122anc.mm"
include "eqtrd.mm"

theorem cdlemg2fv2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ F e. T ) -> ( F ` ( R .\/ U ) ) = ( ( F ` R ) .\/ U ) )

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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cR
    cU
    c.or
    co
    #
    cF
    cfv
    #
    cR
    cF
    cfv
    #
    @16
    cW
    c.an
    co
    #
    c.or
    co
    #
    @18
    cU
    c.or
    co
    @15
    @2
    @12
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    @16
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    @14
    cR
    @19
    c.or
    co
    @16
    wceq
    @17
    @20
    wceq
    @2
    @13
    @14
    simp1
    #
    @2
    @5
    @8
    @12
    @14
    simp23
    #
    @15
    @22
    @24
    @15
    cK
    clat
    wcel
    #
    cR
    @21
    wcel
    #
    cU
    @21
    wcel
    #
    @22
    @15
    @0
    @27
    @0
    @1
    @13
    @14
    simp1l
    #
    cK
    hllat
    syl
    #
    @15
    @9
    @28
    @9
    @11
    @5
    @8
    @2
    @14
    simp23l
    #
    cA
    @21
    cR
    cK
    @21
    eqid
    #
    cdlemg2j.a
    atbase
    syl
    #
    @15
    @0
    @1
    @3
    @6
    @29
    @30
    @0
    @1
    @13
    @14
    simp1r
    #
    @3
    @4
    @8
    @12
    @2
    @14
    simp21l
    #
    @6
    @7
    @5
    @12
    @2
    @14
    simp22l
    #
    cA
    @21
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
    @33
    cdleme0aa
    syl211anc
    #
    @21
    c.or
    cK
    cR
    cU
    @33
    cdlemg2j.j
    latjcl
    syl3anc
    #
    @15
    @23
    @10
    @9
    @11
    @5
    @8
    @2
    @14
    simp23r
    @15
    cR
    @16
    c.le
    wbr
    #
    @23
    @10
    @15
    @27
    @28
    @29
    @40
    @31
    @34
    @38
    @21
    c.or
    cK
    c.le
    cR
    cU
    @33
    cdlemg2j.l
    cdlemg2j.j
    latlej1
    syl3anc
    @15
    @27
    @28
    @22
    cW
    @21
    wcel
    #
    @40
    @23
    wa
    @10
    wi
    @31
    @34
    @39
    @15
    @1
    @41
    @35
    @21
    cH
    cK
    cW
    @33
    cdlemg2inv.h
    lhpbase
    syl
    #
    @21
    cK
    c.le
    cR
    @16
    cW
    @33
    cdlemg2j.l
    lattr
    syl13anc
    mpand
    mtod
    jca
    @2
    @13
    @14
    simp3
    @15
    @19
    cU
    cR
    c.or
    @15
    cR
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
    @19
    cU
    @15
    @43
    @45
    cU
    c.or
    @15
    @2
    @12
    @43
    @45
    wceq
    @25
    @26
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @45
    cdlemg2j.l
    cdlemg2j.m
    @45
    eqid
    #
    cdlemg2j.a
    cdlemg2inv.h
    lhpmat
    syl2anc
    oveq1d
    @15
    @0
    @9
    @29
    @41
    cU
    cW
    c.le
    wbr
    @44
    @19
    wceq
    @30
    @32
    @38
    @42
    @15
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
    @15
    @27
    @48
    @21
    wcel
    #
    @41
    @49
    cW
    c.le
    wbr
    @31
    @15
    @0
    @3
    @6
    @50
    @30
    @36
    @37
    cA
    @21
    c.or
    cK
    cP
    cQ
    @33
    cdlemg2j.j
    cdlemg2j.a
    hlatjcl
    syl3anc
    @42
    @21
    cK
    c.le
    c.an
    @48
    cW
    @33
    cdlemg2j.l
    cdlemg2j.m
    latmle2
    syl3anc
    syl5eqbr
    cA
    @21
    cR
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
    @15
    cK
    col
    wcel
    #
    @29
    @46
    cU
    wceq
    @15
    @0
    @51
    @30
    cK
    hlol
    syl
    @38
    @21
    c.or
    cK
    cU
    @45
    @33
    cdlemg2j.j
    @47
    olj02
    syl2anc
    3eqtr3d
    #
    oveq2d
    cA
    @21
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    @16
    cdlemg2inv.h
    cdlemg2inv.t
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.a
    cdlemg2j.m
    @33
    cdlemg2fv
    syl122anc
    @15
    @19
    cU
    @18
    c.or
    @52
    oveq2d
    eqtrd
end
