include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "oveq12i.mm"
include "col.mm"
include "cbs.mm"
include "simp1l.mm"
include "hlol.mm"
include "syl.mm"
include "simp21l.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp23l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmmdir.mm"
include "syl13anc.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "simp3r.mm"
include "latnlej1r.mm"
include "necomd.mm"
include "syl131anc.mm"
include "simp3.mm"
include "hlatcon3.mm"
include "2llnma2.mm"
include "syl132anc.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "simp1.mm"
include "simp21.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "simp3l.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "latnlej1l.mm"
include "atnem0.mm"
include "mpbird.mm"

theorem cdleme0e
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme0c.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> U =/= V )

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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
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
    wa
    #
    w3a
    #
    cU
    cV
    wne
    #
    cU
    cV
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    wceq
    #
    @15
    @17
    cP
    cW
    c.an
    co
    #
    @18
    @15
    @17
    @12
    cW
    c.an
    co
    #
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.an
    co
    #
    @20
    cU
    @21
    cV
    @23
    c.an
    cdleme0.u
    cdleme0c.3
    oveq12i
    @15
    @12
    @22
    c.an
    co
    #
    cW
    c.an
    co
    #
    @24
    @20
    @15
    cK
    col
    wcel
    #
    @12
    cK
    cbs
    cfv
    #
    wcel
    #
    @22
    @28
    wcel
    #
    cW
    @28
    wcel
    #
    @26
    @24
    wceq
    @15
    @0
    @27
    @0
    @1
    @10
    @14
    simp1l
    #
    cK
    hlol
    syl
    @15
    @0
    @3
    @6
    @29
    @32
    @3
    @4
    @6
    @9
    @2
    @14
    simp21l
    #
    @2
    @5
    @6
    @9
    @14
    simp22
    #
    cA
    @28
    c.or
    cK
    cP
    cQ
    @28
    eqid
    #
    cdleme0.j
    cdleme0.a
    hlatjcl
    syl3anc
    @15
    @0
    @3
    @7
    @30
    @32
    @33
    @7
    @8
    @5
    @6
    @2
    @14
    simp23l
    #
    cA
    @28
    c.or
    cK
    cP
    cR
    @35
    cdleme0.j
    cdleme0.a
    hlatjcl
    syl3anc
    @15
    @1
    @31
    @0
    @1
    @10
    @14
    simp1r
    @28
    cH
    cK
    cW
    @35
    cdleme0.h
    lhpbase
    syl
    @28
    cK
    c.an
    @12
    @22
    cW
    @35
    cdleme0.m
    latmmdir
    syl13anc
    @15
    @25
    cP
    cW
    c.an
    @15
    @0
    @6
    @7
    @3
    cQ
    cR
    wne
    #
    cP
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    @25
    cP
    wceq
    @32
    @34
    @36
    @33
    @15
    cK
    clat
    wcel
    #
    cR
    @28
    wcel
    #
    cP
    @28
    wcel
    #
    cQ
    @28
    wcel
    #
    @13
    @37
    @15
    @0
    @39
    @32
    cK
    hllat
    syl
    #
    @15
    @7
    @40
    @36
    cA
    @28
    cR
    cK
    @35
    cdleme0.a
    atbase
    syl
    #
    @15
    @3
    @41
    @33
    cA
    @28
    cP
    cK
    @35
    cdleme0.a
    atbase
    syl
    #
    @15
    @6
    @42
    @34
    cA
    @28
    cQ
    cK
    @35
    cdleme0.a
    atbase
    syl
    #
    @2
    @10
    @11
    @13
    simp3r
    #
    @39
    @40
    @41
    @42
    w3a
    @13
    w3a
    #
    cR
    cQ
    @28
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @35
    cdleme0.l
    cdleme0.j
    latnlej1r
    necomd
    syl131anc
    @15
    @0
    @3
    @6
    @7
    @14
    @38
    @32
    @33
    @34
    @36
    @2
    @10
    @14
    simp3
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cdleme0.l
    cdleme0.j
    cdleme0.a
    hlatcon3
    syl131anc
    cA
    cQ
    cR
    cP
    c.or
    cK
    c.le
    c.an
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    2llnma2
    syl132anc
    oveq1d
    eqtr3d
    syl5eq
    @15
    @2
    @5
    @20
    @18
    wceq
    @2
    @10
    @14
    simp1
    #
    @2
    @5
    @6
    @9
    @14
    simp21
    #
    cA
    cP
    cH
    cK
    c.le
    c.an
    cW
    @18
    cdleme0.l
    cdleme0.m
    @18
    eqid
    #
    cdleme0.a
    cdleme0.h
    lhpmat
    syl2anc
    eqtrd
    @15
    cK
    cal
    wcel
    #
    cU
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    @16
    @19
    wb
    @15
    @0
    @52
    @32
    cK
    hlatl
    syl
    @15
    @2
    @5
    @6
    @11
    @53
    @49
    @50
    @34
    @2
    @10
    @11
    @13
    simp3l
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    lhpat2
    syl112anc
    @15
    @2
    @5
    @7
    cP
    cR
    wne
    #
    @54
    @49
    @50
    @36
    @15
    @39
    @40
    @41
    @42
    @13
    @55
    @43
    @44
    @45
    @46
    @47
    @48
    cR
    cP
    @28
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @35
    cdleme0.l
    cdleme0.j
    latnlej1l
    necomd
    syl131anc
    cA
    cP
    cR
    cV
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0c.3
    lhpat2
    syl112anc
    cA
    cU
    cV
    cK
    c.an
    @18
    cdleme0.m
    @51
    cdleme0.a
    atnem0
    syl3anc
    mpbird
end
